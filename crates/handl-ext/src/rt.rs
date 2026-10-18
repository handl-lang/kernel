//! Runtime support invoked by the [`crate::export!`] macro.
//!
//! This module is `#[doc(hidden)]` machinery — the stable surface for
//! extension authors is `export!` plus the manifest/request/response types.
//! Everything here is written so the exported `extern "C"` wrappers stay
//! total: bad input produces a JSON error response, panics are caught, and
//! no code path returns a null pointer.

use std::ffi::{CStr, CString, c_char};
use std::panic::{AssertUnwindSafe, catch_unwind};

use crate::{ExtRequest, ExtResponse, ExtensionManifest};

/// `EX_SOFTWARE` (sysexits.h): an extension panicked mid-dispatch.
const EX_SOFTWARE: i32 = 70;

/// Serialize `f()`'s manifest to a heap-allocated C string.
///
/// On any internal failure (panic in `f`, serialization error — both should
/// be impossible for a well-formed manifest) a minimal valid manifest JSON
/// is returned so the host never sees null.
pub fn manifest_ptr(f: impl FnOnce() -> ExtensionManifest) -> *mut c_char {
    let json = catch_unwind(AssertUnwindSafe(|| {
        serde_json::to_string(&f()).unwrap_or_else(|_| fallback_manifest())
    }))
    .unwrap_or_else(|_| fallback_manifest());
    into_raw(json)
}

/// Read `cmd`/`input`, deserialize the [`ExtRequest`], run `f`, serialize
/// its [`ExtResponse`].
///
/// # Safety
///
/// `cmd` and `input` must be valid NUL-terminated strings or null. Anything
/// else — null, non-UTF-8, non-JSON, a panicking `f` — yields a JSON
/// [`ExtResponse`] describing the problem rather than UB or null.
///
/// # Panics
///
/// Never panics across the FFI boundary: `f` runs under `catch_unwind` and
/// every fallible step has a defined error response.
pub unsafe fn dispatch_ptr(
    cmd: *const c_char,
    input: *const c_char,
    f: impl Fn(&str, &ExtRequest) -> ExtResponse,
) -> *mut c_char {
    let response = catch_unwind(AssertUnwindSafe(|| dispatch_inner(cmd, input, &f)))
        .unwrap_or_else(|panic| {
            ExtResponse::error(
                EX_SOFTWARE,
                format!("extension panicked: {}", panic_msg(&*panic)),
            )
        });
    into_raw(serde_json::to_string(&response).unwrap_or_else(|_| {
        // `ExtResponse` is flat strings + int — unreachable in practice, but
        // the ABI promises a valid JSON response no matter what.
        "{\"code\":70,\"stdout\":\"\",\"stderr\":\"extension failed to encode response\"}".to_string()
    }))
}

/// Release a `char*` previously returned by `manifest_ptr`/`dispatch_ptr`.
///
/// # Safety
///
/// `s` must be a pointer handed out by this extension (allocated via
/// `CString::into_raw` here) or null.
pub unsafe fn free_ptr(s: *mut c_char) {
    if !s.is_null() {
        // Reconstruct the CString so its allocation is freed exactly once.
        drop(unsafe { CString::from_raw(s) });
    }
}

// ---------------------------------------------------------------------------
// Internals
// ---------------------------------------------------------------------------

/// The fallible part of [`dispatch_ptr`], kept separate so `catch_unwind`
/// wraps exactly the work that can fail.
fn dispatch_inner(
    cmd: *const c_char,
    input: *const c_char,
    f: &impl Fn(&str, &ExtRequest) -> ExtResponse,
) -> ExtResponse {
    let Some(cmd) = (unsafe { c_str_arg(cmd) }) else {
        return ExtResponse::error(2, "handl-ext: dispatch called with a null command");
    };
    let Some(input) = (unsafe { c_str_arg(input) }) else {
        return ExtResponse::error(2, "handl-ext: dispatch called with null input");
    };
    let request: ExtRequest = match serde_json::from_str(input) {
        Ok(r) => r,
        Err(e) => {
            return ExtResponse::error(2, format!("handl-ext: malformed request JSON: {e}"));
        }
    };
    f(&cmd, &request)
}

/// Borrow a `*const c_char` as `&str`; `None` on null or invalid UTF-8.
///
/// # Safety
///
/// When non-null, `p` must point to a NUL-terminated string that outlives
/// the borrow.
unsafe fn c_str_arg<'a>(p: *const c_char) -> Option<&'a str> {
    if p.is_null() {
        return None;
    }
    // Safety: upheld by the caller contract documented on this fn.
    unsafe { CStr::from_ptr(p) }.to_str().ok()
}

/// Extract a human-readable message from a `catch_unwind` payload.
fn panic_msg(payload: &dyn std::any::Any) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "unknown panic".to_string()
    }
}

/// Move `json` onto the heap as a NUL-terminated string, giving ownership
/// to the caller (which must return it via [`free_ptr`]).
///
/// JSON never contains a NUL byte, so `CString::new` cannot fail; the
/// fallback keeps the contract total anyway.
fn into_raw(json: String) -> *mut c_char {
    match CString::new(json) {
        Ok(s) => s.into_raw(),
        Err(_) => CString::new("{}")
            .expect("static NUL-free literal")
            .into_raw(),
    }
}

/// Last-ditch manifest when building or serializing the real one failed.
fn fallback_manifest() -> String {
    "{\"name\":\"<error>\",\"version\":\"\",\"commands\":[]}".to_string()
}
