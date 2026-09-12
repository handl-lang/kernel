//! Capability set derivation (ADR-0044 §7 safety, ADR-0052 kernel).
//!
//! A `Language`'s capability set is the transitive closure of `Foreign`
//! source names across all its eval schemes, plus any explicitly declared
//! capabilities. This makes "does this `Language` touch the filesystem?" a
//! static data query — no runtime sandbox required for a pure `Language`.
//!
//! In the arrow-calculus kernel the capability boundary is structural: an
//! `Arr` with `source: Foreign(name)` is capability-tracked (matched on by
//! the typechecker and the load-time capability audit), not a string prefix
//! convention.

use std::collections::BTreeSet;

use plugin_engine::TermData;

use crate::fragment::Fragment;
use crate::language::Language;
use crate::term::{ArrSource, Term};

/// Recursively walk a [`Term`] and collect every `Foreign(name)` source
/// name.
///
/// Walks every `Term` node (recursing into `args`, `Seq`, `First`,
/// `Choice`, `Loop`, and `App` children) and collects each foreign name.
pub fn foreign_names(scheme: &Term) -> BTreeSet<String> {
    let td = TermData::from_term(scheme);
    let mut out = BTreeSet::new();
    collect_foreign_td(&td, &mut out);
    out
}

/// Data-driven counterpart of `collect_foreign`, operating on [`TermData`].
///
/// Dispatches on `td.tag()` and accesses fields via `get_term` /
/// `get_term_list` / `arr_source`, recursing into child terms.
fn collect_foreign_td(td: &TermData, out: &mut BTreeSet<String>) {
    match td.tag() {
        "Op" => {
            if let Some(ArrSource::Foreign(name)) = td.arr_source() {
                out.insert(name);
            }
            for a in td.get_term_list("args") {
                collect_foreign_td(&a, out);
            }
        }
        "Seq" => {
            let fst = td.get_term("fst").expect("Seq: missing fst");
            let snd = td.get_term("snd").expect("Seq: missing snd");
            collect_foreign_td(&fst, out);
            collect_foreign_td(&snd, out);
        }
        "First" => {
            let inner = td.get_term("inner").expect("First: missing inner");
            collect_foreign_td(&inner, out);
        }
        "Choice" => {
            let l = td.get_term("l").expect("Choice: missing l");
            let r = td.get_term("r").expect("Choice: missing r");
            collect_foreign_td(&l, out);
            collect_foreign_td(&r, out);
        }
        "Loop" => {
            let body = td.get_term("body").expect("Loop: missing body");
            collect_foreign_td(&body, out);
        }
        "App" => {
            let callee = td.get_term("callee").expect("App: missing callee");
            collect_foreign_td(&callee, out);
            for a in td.get_term_list("args") {
                collect_foreign_td(&a, out);
            }
        }
        "Handle" => {
            let body = td.get_term("body").expect("Handle: missing body");
            let impl_ = td.get_term("impl_").expect("Handle: missing impl_");
            collect_foreign_td(&body, out);
            collect_foreign_td(&impl_, out);
        }
        "Rewrite" => {
            let source = td.get_term("source").expect("Rewrite: missing source");
            let target = td.get_term("target").expect("Rewrite: missing target");
            collect_foreign_td(&source, out);
            collect_foreign_td(&target, out);
        }
        "Arr" | "Child" | "Const" => {}
        "Iter" => {
            let fuel = td.get_term("fuel").expect("Iter: missing fuel");
            let predicate = td.get_term("predicate").expect("Iter: missing predicate");
            let step = td.get_term("step").expect("Iter: missing step");
            let initial = td.get_term("initial").expect("Iter: missing initial");
            collect_foreign_td(&fuel, out);
            collect_foreign_td(&predicate, out);
            collect_foreign_td(&step, out);
            collect_foreign_td(&initial, out);
        }
        "Path" => {
            let from = td.get_term("from").expect("Path: missing from");
            let to = td.get_term("to").expect("Path: missing to");
            collect_foreign_td(&from, out);
            collect_foreign_td(&to, out);
            if let Some(witness) = td.get_term("witness") {
                if !witness.as_value().is_null() {
                    collect_foreign_td(&witness, out);
                }
            }
        }
        "Equiv" => {
            let a = td.get_term("a").expect("Equiv: missing a");
            let b = td.get_term("b").expect("Equiv: missing b");
            collect_foreign_td(&a, out);
            collect_foreign_td(&b, out);
            if let Some(path) = td.get_term("path") {
                if !path.as_value().is_null() {
                    collect_foreign_td(&path, out);
                }
            }
        }
        "Src" => {
            let cell = td.get_term("cell").expect("Src: missing cell");
            collect_foreign_td(&cell, out);
        }
        "Tgt" => {
            let cell = td.get_term("cell").expect("Tgt: missing cell");
            collect_foreign_td(&cell, out);
        }
        "RecordProj" => {
            let record = td.get_term("record").expect("RecordProj: missing record");
            collect_foreign_td(&record, out);
        }
        "RecordWith" => {
            let record = td.get_term("record").expect("RecordWith: missing record");
            let value = td.get_term("value").expect("RecordWith: missing value");
            collect_foreign_td(&record, out);
            collect_foreign_td(&value, out);
        }
        "Tag" => {
            let value = td.get_term("value").expect("Tag: missing value");
            collect_foreign_td(&value, out);
        }
        "CellId" => {
            let arrow = td.get_term("arrow").expect("CellId: missing arrow");
            collect_foreign_td(&arrow, out);
        }
        "CellCompV" => {
            let first = td.get_term("first").expect("CellCompV: missing first");
            let second = td.get_term("second").expect("CellCompV: missing second");
            collect_foreign_td(&first, out);
            collect_foreign_td(&second, out);
        }
        "Whisker" => {
            let arrow = td.get_term("arrow").expect("Whisker: missing arrow");
            let cell = td.get_term("cell").expect("Whisker: missing cell");
            collect_foreign_td(&arrow, out);
            collect_foreign_td(&cell, out);
        }
        "Univalence" => {
            let equiv = td.get_term("equiv").expect("Univalence: missing equiv");
            collect_foreign_td(&equiv, out);
        }
        "Glue" => {
            let family = td.get_term("family").expect("Glue: missing family");
            let path = td.get_term("path").expect("Glue: missing path");
            collect_foreign_td(&family, out);
            collect_foreign_td(&path, out);
        }
        "Fibrant" => {
            let base = td.get_term("base").expect("Fibrant: missing base");
            let family = td.get_term("family").expect("Fibrant: missing family");
            collect_foreign_td(&base, out);
            collect_foreign_td(&family, out);
        }
        "JElim" => {
            let path = td.get_term("path").expect("JElim: missing path");
            let motive = td.get_term("motive").expect("JElim: missing motive");
            let base = td.get_term("base").expect("JElim: missing base");
            collect_foreign_td(&path, out);
            collect_foreign_td(&motive, out);
            collect_foreign_td(&base, out);
        }
        "Refine" => {
            let sort = td.get_term("sort").expect("Refine: missing sort");
            let predicate = td.get_term("predicate").expect("Refine: missing predicate");
            collect_foreign_td(&sort, out);
            collect_foreign_td(&predicate, out);
        }
        "Cobind" => {
            let grade = td.get_term("grade").expect("Cobind: missing grade");
            let body = td.get_term("body").expect("Cobind: missing body");
            collect_foreign_td(&grade, out);
            collect_foreign_td(&body, out);
        }
        // Unknown / malformed tags: no foreign names to collect.
        _ => {}
    }
}

/// Compute the full capability set of a [`Language`]: the union of all
/// `Foreign` names across its eval schemes plus its explicitly declared
/// capabilities.
pub fn capabilities(lang: &Language) -> BTreeSet<String> {
    lang.eval
        .fragments()
        .flat_map(|scheme| foreign_names(&scheme.scheme))
        .chain(lang.caps.iter().map(|c| c.id().to_string()))
        .collect()
}

/// Whether every capability in `needed` is contained in `allowed`.
///
/// Used by a sandbox to verify `capabilities(mod_lang).subset_of(allowed)` at
/// load time.
pub fn subset_of(needed: &BTreeSet<String>, allowed: &BTreeSet<String>) -> bool {
    needed.iter().all(|c| allowed.contains(c))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fragments::{CapabilityDecl, EvalSchemeDef};
    use crate::language::Language;
    use serde_json::Value;

    /// Convert `TermData` back to `Term` for APIs that require `Term`.
    fn t(td: TermData) -> Term {
        td.to_term().expect("TermData -> Term conversion")
    }

    /// Native op without a literal payload (mirrors `TermData::op`).
    fn op_native(name: &str, args: Vec<TermData>) -> TermData {
        if name == "const" && args.is_empty() {
            TermData::arr(Value::Null)
        } else {
            TermData::op(name, args, &ArrSource::Native, None)
        }
    }

    /// Native op with a literal payload (mirrors `TermData::op`).
    fn op_lit(name: &str, args: Vec<TermData>, lit: impl Into<Value>) -> TermData {
        if name == "const" && args.is_empty() {
            TermData::arr(lit.into())
        } else {
            TermData::op(name, args, &ArrSource::Native, Some(lit.into()))
        }
    }

    /// Foreign op (mirrors `TermData::op`).
    fn op_foreign(name: &str, args: Vec<TermData>) -> TermData {
        TermData::op(name, args, &ArrSource::Foreign(name.to_string()), None)
    }

    #[test]
    fn foreign_names_collects_recursively() {
        let s = t(TermData::choice(
            op_foreign(
                "fs.read",
                vec![op_foreign("fs.open", vec![])],
            ),
            TermData::app(
                op_foreign("net.send", vec![]),
                vec![op_native("id", vec![])],
            ),
        ));
        let names = foreign_names(&s);
        assert!(names.contains("fs.read"));
        assert!(names.contains("fs.open"));
        assert!(names.contains("net.send"));
        assert_eq!(names.len(), 3);
    }

    #[test]
    fn no_foreign_returns_empty() {
        let s = t(op_native(
            "add",
            vec![op_native("id", vec![])],
        ));
        assert!(foreign_names(&s).is_empty());
    }

    #[test]
    fn capabilities_combines_foreign_and_declared() {
        let mut lang = Language::new();
        lang.eval
            .merge(EvalSchemeDef::new(
                "eval.io",
                "io",
                t(op_foreign(
                    "fs.read",
                    vec![op_lit(
                        "proj_child",
                        vec![],
                        Value::from(0u64),
                    )],
                )),
            ))
            .unwrap();
        lang.caps.merge(CapabilityDecl::new("net.connect")).unwrap();
        let caps = capabilities(&lang);
        assert!(caps.contains("fs.read"));
        assert!(caps.contains("net.connect"));
        assert_eq!(caps.len(), 2);
    }

    #[test]
    fn no_foreign_language_returns_only_declared() {
        let mut lang = Language::new();
        lang.eval
            .merge(EvalSchemeDef::new(
                "eval.add",
                "binary.add",
                t(op_native(
                    "add",
                    vec![
                        op_lit("proj_child", vec![], Value::from(0u64)),
                        op_lit("proj_child", vec![], Value::from(1u64)),
                    ],
                )),
            ))
            .unwrap();
        lang.caps.merge(CapabilityDecl::new("pure")).unwrap();
        let caps = capabilities(&lang);
        assert_eq!(caps, ["pure".to_string()].into_iter().collect());
    }

    #[test]
    fn subset_of_passes() {
        let needed: BTreeSet<String> = ["a", "b"].into_iter().map(String::from).collect();
        let allowed: BTreeSet<String> = ["a", "b", "c"].into_iter().map(String::from).collect();
        assert!(subset_of(&needed, &allowed));
    }

    #[test]
    fn subset_of_fails() {
        let needed: BTreeSet<String> = ["a", "d"].into_iter().map(String::from).collect();
        let allowed: BTreeSet<String> = ["a", "b", "c"].into_iter().map(String::from).collect();
        assert!(!subset_of(&needed, &allowed));
    }

    #[test]
    fn subset_of_empty_needed_passes() {
        let allowed: BTreeSet<String> = ["a"].into_iter().map(String::from).collect();
        assert!(subset_of(&BTreeSet::new(), &allowed));
    }

    #[test]
    fn foreign_names_nested_seq_loop() {
        let s = t(TermData::seq(
            TermData::loop_feedback(op_foreign("fs.read", vec![])),
            TermData::first(op_foreign("net.send", vec![])),
        ));
        let names = foreign_names(&s);
        assert!(names.contains("fs.read"));
        assert!(names.contains("net.send"));
        assert_eq!(names.len(), 2);
    }
}
