//! Atom-provider wire convention (P-013 phase-2c, proposal-0012).
//!
//! An extension becomes an **atom provider** by setting
//! [`ExtensionManifest::atoms_yaml`](crate::ExtensionManifest::atoms_yaml)
//! in its manifest — the extension's own `atoms.yaml` text, parsed by the
//! host for the module names it claims. Atom *calls* reuse the ordinary
//! `handl_ext_dispatch` entry point; no extra ABI symbols are added:
//!
//! ```text
//! host → ext:  handl_ext_dispatch(cmd = "<module>.<atom>",   # e.g. "tensor.zeros"
//!                                 input = ExtRequest {
//!                                     args: ["<json array of call args>"],
//!                                     cwd, env })
//! ext  → host: ExtResponse {
//!     code:   0  → stdout is the serde_json::Value result, verbatim
//!     code: !=0  → stderr is the failure message (stdout ignored)
//! }
//! ```
//!
//! The single `args[0]` payload is a JSON array because [`ExtRequest::args`]
//! is `Vec<String>` — atom arguments are arbitrary `serde_json::Value`s,
//! not strings. [`atom_call_args`] decodes it provider-side;
//! [`atom_result`]/[`atom_failure`] encode the reply.
//!
//! Provider skeleton:
//!
//! ```ignore
//! handl_ext::export!(
//!     handl_ext::ExtensionManifest::new("myprovider")
//!         .version(env!("CARGO_PKG_VERSION"))
//!         .atoms_yaml(include_str!("../atoms.yaml")),
//!     dispatch
//! );
//!
//! fn dispatch(cmd: &str, req: &handl_ext::ExtRequest) -> handl_ext::ExtResponse {
//!     match cmd {
//!         "mymod.echo" => {
//!             let args = match handl_ext::atom_call_args(req) {
//!                 Ok(a) => a,
//!                 Err(r) => return r,
//!             };
//!             handl_ext::atom_result(&args[0])
//!         }
//!         _ => handl_ext::ExtResponse::error(2, format!("unknown atom `{cmd}`")),
//!     }
//! }
//! ```
//!
//! Notes for provider authors:
//!
//! - Atom names are dispatched verbatim — they are *not* declared in
//!   `commands` (they must not appear as CLI commands).
//! - There is no [`EvalContext`](handl_platform::EvalContext) across the
//!   boundary: providers evaluate with a fresh context. Atoms that need
//!   host recursion/module lookup cannot be cdylib providers.
//! - The manifest's `atoms_yaml` is the provider's claim surface; the
//!   *spec actually bound* still comes from the consuming dep's own
//!   `atoms.yaml` (P-013 phase-2a semantics — spec and impls may drift,
//!   and the host's registry build is what catches it).

use serde_json::Value;

use crate::ExtRequest;
use crate::ExtResponse;

/// Decode the atom-call argument payload: `req.args[0]` must be a JSON
/// array of the call's argument values.
///
/// Returns `Err(ExtResponse)` (already shaped for return from `dispatch`)
/// when the payload is missing or malformed — `dispatch` returns
/// `ExtResponse`, not `Result`, so providers `match` (or `unwrap_or_else`)
/// rather than `?`.
pub fn atom_call_args(req: &ExtRequest) -> Result<Vec<Value>, ExtResponse> {
    let Some(payload) = req.args.first() else {
        return Err(ExtResponse::error(
            2,
            "atom call: missing args payload (expected args[0] = JSON array)",
        ));
    };
    serde_json::from_str::<Vec<Value>>(payload).map_err(|e| {
        ExtResponse::error(
            2,
            format!("atom call: args payload is not a JSON array: {e}"),
        )
    })
}

/// Encode a successful atom result: `code: 0`, `stdout` = the
/// `serde_json`-encoded value.
pub fn atom_result(value: &Value) -> ExtResponse {
    ExtResponse {
        code: 0,
        stdout: serde_json::to_string(value).unwrap_or_else(|_| "null".to_string()),
        stderr: String::new(),
    }
}

/// Encode an atom failure: `code: 1`, `stderr` = the message.
pub fn atom_failure(message: impl Into<String>) -> ExtResponse {
    ExtResponse::error(1, message)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn manifest_atoms_yaml_roundtrips() {
        let m = crate::ExtensionManifest::new("p").atoms_yaml("module: x\natoms: []\n");
        let json = serde_json::to_string(&m).unwrap();
        assert!(json.contains("\"atoms_yaml\""));
        let back: crate::ExtensionManifest = serde_json::from_str(&json).unwrap();
        assert_eq!(back.atoms_yaml.as_deref(), Some("module: x\natoms: []\n"));
    }

    #[test]
    fn manifest_without_atoms_yaml_still_parses() {
        // Pre-2c manifests carry no `atoms_yaml` key at all.
        let back: crate::ExtensionManifest =
            serde_json::from_str(r#"{"name":"old","version":"1","commands":[]}"#).unwrap();
        assert_eq!(back.atoms_yaml, None);
    }

    #[test]
    fn call_args_decodes_payload() {
        let req = ExtRequest {
            args: vec![serde_json::to_string(&json!([1, "two", null])).unwrap()],
            ..ExtRequest::default()
        };
        let args = atom_call_args(&req).unwrap();
        assert_eq!(args, vec![json!(1), json!("two"), Value::Null]);
    }

    #[test]
    fn call_args_rejects_missing_and_malformed() {
        assert!(atom_call_args(&ExtRequest::default()).is_err());
        let req = ExtRequest {
            args: vec!["not json".to_string()],
            ..ExtRequest::default()
        };
        assert!(atom_call_args(&req).is_err());
        let req = ExtRequest {
            args: vec!["{\"a\":1}".to_string()],
            ..ExtRequest::default()
        };
        assert!(atom_call_args(&req).is_err());
    }

    #[test]
    fn result_and_failure_shapes() {
        let ok = atom_result(&json!({"v": 42}));
        assert_eq!(ok.code, 0);
        assert_eq!(
            serde_json::from_str::<Value>(&ok.stdout).unwrap(),
            json!({"v": 42})
        );
        let bad = atom_failure("boom");
        assert_eq!(bad.code, 1);
        assert_eq!(bad.stderr, "boom");
    }
}
