//! Tests for the `handl-ext` ABI surface.
//!
//! The dynamic loading path (`LoadedExtension::load`) needs a real cdylib
//! on disk, which `cargo test` cannot synthesize in-process; that path is
//! exercised end-to-end by `host-cli` + `ext-fmt`. What we can do here is
//! call the `export!`-generated symbols directly — the same code the
//! extension's `dlopen`ed entry points run.

use std::collections::BTreeMap;
use std::ffi::{CStr, CString};

use handl_ext::{ExtRequest, ExtResponse, ExtensionManifest};

// One `export!` per crate: the symbols are global. Declaring it in this
// integration test exercises exactly what an ext-* crate writes.
fn test_dispatch(cmd: &str, req: &ExtRequest) -> ExtResponse {
    match cmd {
        "hello" => ExtResponse::ok(format!(
            "hello {} (cwd={})",
            req.args.join(" "),
            req.cwd
        )),
        "fail" => ExtResponse::error(2, "bad usage\n".to_string()),
        "panic" => panic!("deliberate test panic"),
        _ => ExtResponse::error(2, format!("unknown command {cmd}\n")),
    }
}

handl_ext::export!(
    ExtensionManifest::new("test-ext")
        .version("9.9.9")
        .command("hello", "hello [args...]")
        .command("fail", "fail")
        .command("panic", "panic"),
    test_dispatch
);

// `handl_ext_manifest`/`handl_ext_dispatch`/`handl_ext_free` are defined by
// the `export!` call above at this test crate's root — already in scope.

fn take(ptr: *mut std::ffi::c_char) -> String {
    assert!(!ptr.is_null(), "ABI functions must never return null");
    // Safety: `ptr` came from this test binary's exported functions, whose
    // contract is exactly this read-then-free dance.
    let s = unsafe { CStr::from_ptr(ptr) }
        .to_string_lossy()
        .into_owned();
    unsafe { handl_ext_free(ptr) };
    s
}

fn dispatch(cmd: &str, request: &ExtRequest) -> ExtResponse {
    let cmd = CString::new(cmd).unwrap();
    let input = CString::new(serde_json::to_string(request).unwrap()).unwrap();
    // Safety: both CStrings are valid NUL-terminated strings for the call.
    let raw = unsafe { handl_ext_dispatch(cmd.as_ptr(), input.as_ptr()) };
    let json = take(raw);
    serde_json::from_str(&json).expect("response is valid ExtResponse JSON")
}

#[test]
fn manifest_is_valid_manifest_json() {
    let json = take(handl_ext_manifest());
    let manifest: ExtensionManifest = serde_json::from_str(&json).expect("manifest JSON");
    assert_eq!(manifest.name, "test-ext");
    assert_eq!(manifest.version, "9.9.9");
    assert_eq!(
        manifest.commands.iter().map(|c| c.name.as_str()).collect::<Vec<_>>(),
        ["hello", "fail", "panic"]
    );
    assert_eq!(manifest.commands[0].usage, "hello [args...]");
}

#[test]
fn dispatch_round_trips_request_and_response() {
    let mut env = BTreeMap::new();
    env.insert("K".to_string(), "V".to_string());
    let res = dispatch(
        "hello",
        &ExtRequest {
            args: vec!["a".into(), "b".into()],
            cwd: "/work".into(),
            env,
        },
    );
    assert_eq!(res.code, 0);
    assert_eq!(res.stdout, "hello a b (cwd=/work)");
    assert_eq!(res.stderr, "");
}

#[test]
fn dispatch_propagates_error_code_and_stderr() {
    let res = dispatch("fail", &ExtRequest::default());
    assert_eq!(res.code, 2);
    assert_eq!(res.stderr, "bad usage\n");
}

#[test]
fn dispatch_never_returns_null_on_bad_input() {
    // Null command pointer → error response, not UB.
    let input = CString::new("{}").unwrap();
    let raw = unsafe { handl_ext_dispatch(std::ptr::null(), input.as_ptr()) };
    let res: ExtResponse = serde_json::from_str(&take(raw)).unwrap();
    assert_eq!(res.code, 2);

    // Malformed JSON input → error response.
    let cmd = CString::new("hello").unwrap();
    let bad = CString::new("not json").unwrap();
    let raw = unsafe { handl_ext_dispatch(cmd.as_ptr(), bad.as_ptr()) };
    let res: ExtResponse = serde_json::from_str(&take(raw)).unwrap();
    assert_eq!(res.code, 2);
    assert!(res.stderr.contains("malformed request"));
}

#[test]
fn dispatch_catches_panics() {
    let res = dispatch("panic", &ExtRequest::default());
    assert_eq!(res.code, 70);
    assert!(res.stderr.contains("extension panicked"));
    assert!(res.stderr.contains("deliberate test panic"));
}

#[test]
fn manifest_and_request_serde_shapes_match_the_adr() {
    // ADR-0149 pins the wire shapes; lock them in.
    let manifest = ExtensionManifest::new("fmt")
        .version("0.1.0")
        .command("fmt", "fmt [paths...]");
    let v = serde_json::to_value(&manifest).unwrap();
    assert_eq!(
        v,
        serde_json::json!({
            "name": "fmt",
            "version": "0.1.0",
            "commands": [{"name": "fmt", "usage": "fmt [paths...]"}],
        })
    );

    let req = ExtRequest {
        args: vec!["--check".into()],
        cwd: "/w".into(),
        env: BTreeMap::from([("A".into(), "1".into())]),
    };
    let v = serde_json::to_value(&req).unwrap();
    assert_eq!(
        v,
        serde_json::json!({"args": ["--check"], "cwd": "/w", "env": {"A": "1"}})
    );

    let res = ExtResponse::ok("out");
    let v = serde_json::to_value(&res).unwrap();
    assert_eq!(v, serde_json::json!({"code": 0, "stdout": "out", "stderr": ""}));
}

#[test]
fn load_dir_tolerates_missing_and_non_extension_dirs() {
    let scan = handl_ext::load_dir("/nonexistent/dir/for/sure");
    assert!(scan.loaded.is_empty());
    assert!(scan.failures.is_empty());

    // A dir with only non-extension files yields an empty scan, not errors.
    let dir = std::env::temp_dir().join(format!("handl-ext-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("libsomething_else.so"), b"nope").unwrap();
    std::fs::write(dir.join("readme.txt"), b"nope").unwrap();
    let scan = handl_ext::load_dir(&dir);
    assert!(scan.loaded.is_empty());
    assert!(scan.failures.is_empty());
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn is_extension_file_matches_the_naming_convention() {
    use std::env::consts::{DLL_PREFIX, DLL_SUFFIX};
    let good = format!("{DLL_PREFIX}hnl_ext_fmt{DLL_SUFFIX}");
    assert!(handl_ext::is_extension_file(std::path::Path::new(&good)));
    assert!(!handl_ext::is_extension_file(std::path::Path::new("libother.so")));
    assert!(!handl_ext::is_extension_file(std::path::Path::new("hnl_ext_fmt.txt")));
}

#[test]
fn discovery_reports_missing_dirs_without_failing() {
    let d = handl_ext::discover(&[std::path::PathBuf::from(
        "/nonexistent/ext/dir/for/sure",
    )]);
    // The flag dir is recorded even though it does not exist, so
    // `ext doctor` can say "searched, not found".
    assert!(
        d.dirs
            .iter()
            .any(|c| c.path.to_string_lossy().contains("nonexistent"))
    );
    assert!(d.extensions.is_empty());
    assert!(d.failures.is_empty());
}
