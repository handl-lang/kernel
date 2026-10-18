//! `handl-ext` — the shared ABI for `hnl` dynamic extensions (ADR-0149).
//!
//! `host-cli` is a dumb host: it discovers shared libraries named
//! `{DLL_PREFIX}hnl_ext_<name>{DLL_SUFFIX}` (`libhnl_ext_fmt.so`,
//! `hnl_ext_fmt.dll`, …), reads each extension's manifest, and dispatches
//! argv to the command the manifest declares. Tool knowledge lives entirely
//! inside the extension; the host pins nothing.
//!
//! # ABI — JSON over a C boundary
//!
//! Each extension exports exactly three symbols:
//!
//! ```text
//! char* handl_ext_manifest(void)                          → {"name","version","commands":[{name,usage}]}
//! char* handl_ext_dispatch(const char* cmd, const char* input_json)
//!     input  = {"args":[..], "cwd": "..", "env": {..}}
//!     return = {"code": int, "stdout": "..", "stderr": ".."}
//! void  handl_ext_free(char*)                             → frees strings returned by the two above
//! ```
//!
//! Strings returned by an extension are owned by that extension and must be
//! released through *its* `handl_ext_free` — the host never frees across the
//! boundary. JSON keeps Rust-type ABI fragility (`TaggedValue`, `serde_json`
//! layout) inside each side.
//!
//! # For hosts (loading)
//!
//! ```ignore
//! let found = handl_ext::discover(&[extra_dir]);
//! let ext = found.find_command("fmt").expect("fmt extension");
//! let response = ext.dispatch("fmt", &ExtRequest {
//!     args: vec!["--check".into(), "main.hnl".into()],
//!     cwd: "/work".into(),
//!     env: std::env::vars().collect(),
//! })?;
//! ```
//!
//! # For extension authors (exporting)
//!
//! ```ignore
//! fn dispatch(cmd: &str, req: &handl_ext::ExtRequest) -> handl_ext::ExtResponse {
//!     handl_ext::ExtResponse::ok(format!("ran {cmd} with {:?}", req.args))
//! }
//!
//! handl_ext::export!(
//!     handl_ext::ExtensionManifest::new("hello")
//!         .version(env!("CARGO_PKG_VERSION"))
//!         .command("hello", "hello [name...]"),
//!     dispatch
//! );
//! ```

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

mod discovery;
mod load;
pub mod rt;

pub use discovery::{
    CandidateDir, DirSource, Discovery, candidate_dirs, discover, home_ext_dir,
};
pub use load::{DirScan, LoadFailure, LoadedExtension, is_extension_file, load_dir};

// ---------------------------------------------------------------------------
// Manifest (extension → host, via `handl_ext_manifest`)
// ---------------------------------------------------------------------------

/// A command an extension declares in its manifest.
///
/// Multi-word surfaces (`compile js`, `sdkgen c`) stay the extension's own
/// problem: the manifest declares the *first* word (`compile`), the rest
/// arrives in [`ExtRequest::args`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CommandSpec {
    /// The command name the host dispatches on (argv[1]).
    pub name: String,
    /// One-line usage shown by `hnl --help` / `hnl ext list`.
    #[serde(default)]
    pub usage: String,
}

/// What `handl_ext_manifest()` returns: extension identity + its commands.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExtensionManifest {
    /// Extension name (`fmt`, `lint`, …). Matches the `<name>` in
    /// `libhnl_ext_<name>` by convention; not enforced by the ABI.
    pub name: String,
    /// Extension version string (usually `env!("CARGO_PKG_VERSION")`).
    #[serde(default)]
    pub version: String,
    /// Commands this extension serves.
    #[serde(default)]
    pub commands: Vec<CommandSpec>,
}

impl ExtensionManifest {
    /// An empty manifest for `name`.
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            version: String::new(),
            commands: Vec::new(),
        }
    }

    /// Set the version string.
    pub fn version(mut self, version: impl Into<String>) -> Self {
        self.version = version.into();
        self
    }

    /// Declare one command.
    pub fn command(mut self, name: impl Into<String>, usage: impl Into<String>) -> Self {
        self.commands.push(CommandSpec {
            name: name.into(),
            usage: usage.into(),
        });
        self
    }
}

// ---------------------------------------------------------------------------
// Request / response (host → extension and back, via `handl_ext_dispatch`)
// ---------------------------------------------------------------------------

/// The dispatch input: argv after the command name plus host context.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExtRequest {
    /// argv[2..] — the extension parses its own flags.
    #[serde(default)]
    pub args: Vec<String>,
    /// The host process's working directory; extensions resolve relative
    /// paths against this rather than relying on inherited process state.
    #[serde(default)]
    pub cwd: String,
    /// Host environment, verbatim.
    #[serde(default)]
    pub env: BTreeMap<String, String>,
}

/// What `handl_ext_dispatch` returns.
///
/// `stdout`/`stderr` are written to the host's streams verbatim; `code`
/// becomes the process exit code.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExtResponse {
    /// Process exit code (`0` success, `1` check-failure, `2` usage error —
    /// the host applies no meaning beyond propagating it).
    #[serde(default)]
    pub code: i32,
    /// Bytes for the host's stdout.
    #[serde(default)]
    pub stdout: String,
    /// Bytes for the host's stderr.
    #[serde(default)]
    pub stderr: String,
}

impl ExtResponse {
    /// A successful response carrying only stdout.
    pub fn ok(stdout: impl Into<String>) -> Self {
        Self {
            code: 0,
            stdout: stdout.into(),
            stderr: String::new(),
        }
    }

    /// A failing response carrying only stderr.
    pub fn error(code: i32, stderr: impl Into<String>) -> Self {
        Self {
            code,
            stdout: String::new(),
            stderr: stderr.into(),
        }
    }
}

// ---------------------------------------------------------------------------
// Errors (host side)
// ---------------------------------------------------------------------------

/// Failure to load or talk to an extension.
#[derive(Debug, thiserror::Error)]
pub enum ExtError {
    /// `dlopen`/`LoadLibrary` failed.
    #[error("failed to open {path}: {source}")]
    Open {
        /// The library path that failed to load.
        path: std::path::PathBuf,
        /// The platform loader error.
        source: libloading::Error,
    },
    /// A required ABI symbol is missing.
    #[error("{path}: missing or invalid symbol `{symbol}`: {source}")]
    Symbol {
        /// The library path.
        path: std::path::PathBuf,
        /// The symbol that could not be resolved.
        symbol: &'static str,
        /// The platform loader error.
        source: libloading::Error,
    },
    /// `handl_ext_manifest` returned a null pointer.
    #[error("{path}: handl_ext_manifest returned null")]
    NullManifest {
        /// The library path.
        path: std::path::PathBuf,
    },
    /// The manifest string was not valid manifest JSON.
    #[error("{path}: invalid manifest JSON: {source}")]
    Manifest {
        /// The library path.
        path: std::path::PathBuf,
        /// The serde error.
        source: serde_json::Error,
    },
    /// `handl_ext_dispatch` returned a null pointer.
    #[error("{path}: handl_ext_dispatch returned null")]
    NullResponse {
        /// The library path.
        path: std::path::PathBuf,
    },
    /// The dispatch response was not valid response JSON.
    #[error("{path}: invalid response JSON: {source}")]
    Response {
        /// The library path.
        path: std::path::PathBuf,
        /// The serde error.
        source: serde_json::Error,
    },
    /// A request could not be marshalled (interior NUL or serde failure).
    #[error("failed to marshal dispatch request: {0}")]
    Marshal(String),
}

// ---------------------------------------------------------------------------
// export! — the extension-author side
// ---------------------------------------------------------------------------

/// Export the three ADR-0149 ABI symbols for this crate.
///
/// - `$manifest` — an expression evaluated per `handl_ext_manifest()` call,
///   of type [`ExtensionManifest`].
/// - `$dispatch` — a `fn(&str, &ExtRequest) -> ExtResponse` (path or closure).
///
/// Place at crate root of a `cdylib`:
///
/// ```ignore
/// handl_ext::export!(
///     handl_ext::ExtensionManifest::new("fmt")
///         .version(env!("CARGO_PKG_VERSION"))
///         .command("fmt", "fmt [--check] [--write] [paths...]"),
///     my_dispatch
/// );
/// ```
///
/// The generated `handl_ext_dispatch` catches panics (reported as
/// `{"code": 70, "stderr": "extension panicked: …"}`) and never returns null.
#[macro_export]
macro_rules! export {
    ($manifest:expr, $dispatch:expr) => {
        /// ABI entry point: return the extension manifest JSON.
        ///
        /// The returned string is owned by this extension; the host must
        /// release it via [`handl_ext_free`].
        #[unsafe(no_mangle)]
        pub extern "C" fn handl_ext_manifest() -> *mut ::std::ffi::c_char {
            $crate::rt::manifest_ptr(|| $manifest)
        }

        /// ABI entry point: run `cmd` with the JSON-encoded [`ExtRequest`].
        ///
        /// # Safety
        ///
        /// `cmd` and `input` must be valid NUL-terminated UTF-8 strings (or
        /// null, which is reported as a usage error rather than dereferenced
        /// unconditionally). The returned string is owned by this extension;
        /// the host must release it via [`handl_ext_free`].
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn handl_ext_dispatch(
            cmd: *const ::std::ffi::c_char,
            input: *const ::std::ffi::c_char,
        ) -> *mut ::std::ffi::c_char {
            unsafe { $crate::rt::dispatch_ptr(cmd, input, $dispatch) }
        }

        /// ABI entry point: release a string returned by this extension.
        ///
        /// # Safety
        ///
        /// `s` must be a pointer previously returned by `handl_ext_manifest`
        /// or `handl_ext_dispatch` of *this* library, or null.
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn handl_ext_free(s: *mut ::std::ffi::c_char) {
            unsafe { $crate::rt::free_ptr(s) }
        }
    };
}
