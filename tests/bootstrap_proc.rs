//! # bootstrap_proc.rs — ADR-0052 Phase D arrow-notation bootstrap test
//!
//! Tests that the **arrow-authored** bootstrap source file
//! (`data/handl-defining-handl-proc.hnl`) evaluates to the same result as
//! the v1 bootstrap (`data/handl-defining-handl.hnl`): `3`.
//!
//! The arrow-authored version binds the runtime to `lang` and runs the
//! `eval(lang, parse(lang, lex(lang, "1 + 2")))` pipeline:
//!
//! ```text
//! do { lang = self; eval(lang, parse(lang, lex(lang, "1 + 2"))) }
//! ```
//!
//! It originally used the removed pipe form `self |> lang ~> …` (ADR-0074),
//! which is why this test sat behind an `#[ignore]`; the `do {}` binding is the
//! canonical replacement, so the test is live again.

use handl_kit_canonical::Kit;

/// The arrow-authored bootstrap evaluates to `3`, matching the v1 bootstrap.
#[test]
fn proc_bootstrap_self_host() {
    let source = include_str!("../data/handl-defining-handl-proc.hnl");
    let kit = Kit::new().expect("kit must assemble");
    let result = kit.run(source).expect("arrow bootstrap must succeed");
    assert_eq!(
        result,
        serde_json::json!(3),
        "arrow-authored bootstrap should return 3, got: {}",
        result,
    );
}
