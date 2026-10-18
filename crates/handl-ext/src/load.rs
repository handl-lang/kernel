//! Host side: `dlopen` an extension, read its manifest, dispatch to it.
//!
//! Loading is eager at startup but shallow: [`load_dir`] calls each
//! candidate's `handl_ext_manifest` once and keeps the handle — no tool code
//! runs until [`LoadedExtension::dispatch`] is invoked (ADR-0149 §5).

use std::ffi::{CStr, CString, OsStr, c_char};
use std::path::{Path, PathBuf};

use crate::{ExtError, ExtRequest, ExtResponse, ExtensionManifest};

/// `handl_ext_manifest() -> char*`.
type ManifestFn = unsafe extern "C" fn() -> *mut c_char;
/// `handl_ext_dispatch(cmd, input_json) -> char*`.
type DispatchFn = unsafe extern "C" fn(*const c_char, *const c_char) -> *mut c_char;
/// `handl_ext_free(char*)`.
type FreeFn = unsafe extern "C" fn(*mut c_char);

const MANIFEST_SYM: &[u8] = b"handl_ext_manifest";
const DISPATCH_SYM: &[u8] = b"handl_ext_dispatch";
const FREE_SYM: &[u8] = b"handl_ext_free";

/// An extension shared library kept loaded for the process lifetime.
///
/// The manifest is read once at load; `dispatch` calls cross the boundary
/// per command invocation.
pub struct LoadedExtension {
    path: PathBuf,
    manifest: ExtensionManifest,
    manifest_fn: ManifestFn,
    dispatch_fn: DispatchFn,
    free_fn: FreeFn,
    // Kept alive for the struct's lifetime so the function pointers above
    // stay valid; we never call them in `Drop`.
    #[allow(dead_code)]
    lib: libloading::Library,
}

impl std::fmt::Debug for LoadedExtension {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LoadedExtension")
            .field("path", &self.path)
            .field("manifest", &self.manifest)
            .finish_non_exhaustive()
    }
}

impl LoadedExtension {
    /// Open the library at `path`, resolve the three ABI symbols, and read
    /// its manifest.
    ///
    /// # Errors
    ///
    /// [`ExtError::Open`] when the loader rejects the file,
    /// [`ExtError::Symbol`] when an ABI symbol is missing,
    /// [`ExtError::NullManifest`]/[`ExtError::Manifest`] when the manifest
    /// call or its JSON is bad.
    pub fn load(path: impl AsRef<Path>) -> Result<Self, ExtError> {
        let path = path.as_ref().to_path_buf();
        // Safety: loading an arbitrary shared library runs its initializers;
        // that is inherent to the extension mechanism and is why discovery is
        // limited to explicit dirs, $HANDL_EXT_DIR, ~/.handl/ext, and dev
        // target dirs.
        let lib = unsafe { libloading::Library::new(&path) }.map_err(|source| {
            ExtError::Open {
                path: path.clone(),
                source,
            }
        })?;

        let sym = |name: &'static [u8]| -> Result<*mut std::ffi::c_void, ExtError> {
            // Safety: `lib` outlives the copied pointer (stored below).
            let s: libloading::Symbol<*mut std::ffi::c_void> =
                unsafe { lib.get(name) }.map_err(|source| ExtError::Symbol {
                    path: path.clone(),
                    symbol: std::str::from_utf8(name).unwrap_or("<abi>"),
                    source,
                })?;
            Ok(*s)
        };

        // Copy the raw entry points out of the symbols; they stay valid for
        // as long as `lib` is loaded (the lifetime of this struct).
        let manifest_fn: ManifestFn = unsafe { std::mem::transmute(sym(MANIFEST_SYM)?) };
        let dispatch_fn: DispatchFn = unsafe { std::mem::transmute(sym(DISPATCH_SYM)?) };
        let free_fn: FreeFn = unsafe { std::mem::transmute(sym(FREE_SYM)?) };

        let ext = Self {
            path,
            manifest: ExtensionManifest::new("<unread>"),
            manifest_fn,
            dispatch_fn,
            free_fn,
            lib,
        };
        let manifest = ext.read_manifest()?;
        Ok(Self { manifest, ..ext })
    }

    /// The manifest read at load time.
    pub fn manifest(&self) -> &ExtensionManifest {
        &self.manifest
    }

    /// The library file this extension was loaded from.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Command names this extension declares.
    pub fn command_names(&self) -> impl Iterator<Item = &str> {
        self.manifest.commands.iter().map(|c| c.name.as_str())
    }

    /// Run `command` with `request`, returning the extension's response.
    ///
    /// The returned `char*` is converted and released through the
    /// extension's own `handl_ext_free` — strings are owned by the
    /// allocating side (ADR-0149 §3).
    ///
    /// # Errors
    ///
    /// [`ExtError::Marshal`] when the request cannot be encoded,
    /// [`ExtError::NullResponse`] when the extension returns null,
    /// [`ExtError::Response`] when the reply is not valid response JSON.
    pub fn dispatch(&self, command: &str, request: &ExtRequest) -> Result<ExtResponse, ExtError> {
        let cmd = CString::new(command)
            .map_err(|e| ExtError::Marshal(format!("command contains NUL: {e}")))?;
        let input = CString::new(
            serde_json::to_string(request)
                .map_err(|e| ExtError::Marshal(format!("request encode: {e}")))?,
        )
        .map_err(|e| ExtError::Marshal(format!("request contains NUL: {e}")))?;

        // Safety: `dispatch_fn`/`free_fn` come from this library and were
        // resolved at load; both CStrings are valid NUL-terminated strings.
        let raw = unsafe { (self.dispatch_fn)(cmd.as_ptr(), input.as_ptr()) };
        if raw.is_null() {
            return Err(ExtError::NullResponse {
                path: self.path.clone(),
            });
        }
        let json = unsafe { self.take_string(raw) };
        serde_json::from_str(&json).map_err(|source| ExtError::Response {
            path: self.path.clone(),
            source,
        })
    }

    /// Call `handl_ext_manifest` and parse the result.
    fn read_manifest(&self) -> Result<ExtensionManifest, ExtError> {
        // Safety: `manifest_fn` was resolved from this library at load.
        let raw = unsafe { (self.manifest_fn)() };
        if raw.is_null() {
            return Err(ExtError::NullManifest {
                path: self.path.clone(),
            });
        }
        let json = unsafe { self.take_string(raw) };
        serde_json::from_str(&json).map_err(|source| ExtError::Manifest {
            path: self.path.clone(),
            source,
        })
    }

    /// Copy a `char*` into an owned `String`, then release it through the
    /// extension's `handl_ext_free`.
    ///
    /// # Safety
    ///
    /// `raw` must be a non-null pointer returned by this extension's
    /// manifest/dispatch entry points.
    unsafe fn take_string(&self, raw: *mut c_char) -> String {
        // Safety: per contract the pointer is NUL-terminated and owned by
        // the extension until freed. Copy first — freeing before reading
        // would be use-after-free.
        let s = unsafe { CStr::from_ptr(raw) }
            .to_string_lossy()
            .into_owned();
        // Safety: `raw` came from this extension, so its `free_fn` is the
        // matching deallocator.
        unsafe { (self.free_fn)(raw) };
        s
    }
}

/// A library file that matched the `hnl_ext_*` naming convention but failed
/// to load — surfaced by `hnl ext doctor`.
#[derive(Debug)]
pub struct LoadFailure {
    /// The file that could not be loaded.
    pub path: PathBuf,
    /// Why it failed.
    pub error: ExtError,
}

/// Result of scanning one directory for extensions.
#[derive(Debug, Default)]
pub struct DirScan {
    /// Successfully loaded extensions, in directory order.
    pub loaded: Vec<LoadedExtension>,
    /// Files that matched the naming convention but failed to load.
    pub failures: Vec<LoadFailure>,
}

/// True when `path` looks like an extension library:
/// `{DLL_PREFIX}hnl_ext_*{DLL_SUFFIX}` (`libhnl_ext_fmt.so`,
/// `libhnl_ext_fmt.dylib`, `hnl_ext_fmt.dll`).
pub fn is_extension_file(path: &Path) -> bool {
    let Some(name) = path.file_name().and_then(OsStr::to_str) else {
        return false;
    };
    let prefix = format!("{}hnl_ext_", std::env::consts::DLL_PREFIX);
    name.starts_with(&prefix) && name.ends_with(std::env::consts::DLL_SUFFIX)
}

/// Scan `dir` (non-recursively) for `hnl_ext_*` libraries and load each.
///
/// Missing/unreadable directories produce an empty scan — discovery treats
/// absent dirs as "no extensions there", not as errors (see
/// [`crate::Discovery::dirs`] for per-dir status reporting).
pub fn load_dir(dir: impl AsRef<Path>) -> DirScan {
    let mut scan = DirScan::default();
    let Ok(entries) = std::fs::read_dir(dir) else {
        return scan;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if !path.is_file() || !is_extension_file(&path) {
            continue;
        }
        match LoadedExtension::load(&path) {
            Ok(ext) => scan.loaded.push(ext),
            Err(error) => scan.failures.push(LoadFailure { path, error }),
        }
    }
    scan
}
