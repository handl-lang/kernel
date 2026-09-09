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

use crate::fragment::Fragment;
use crate::language::Language;
use crate::term::{ArrSource, Term};

/// Recursively walk a [`Term`] and collect every `Foreign(name)` source
/// name.
///
/// Walks every `Term` node (recursing into `args`, `Seq`, `First`,
/// `Choice`, `Loop`, and `App` children) and collects each foreign name.
pub fn foreign_names(scheme: &Term) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    collect_foreign(scheme, &mut out);
    out
}

fn collect_foreign(scheme: &Term, out: &mut BTreeSet<String>) {
    match scheme {
        Term::Op { args, source, .. } => {
            if let ArrSource::Foreign(name) = source {
                out.insert(name.clone());
            }
            for a in args {
                collect_foreign(a, out);
            }
        }
        Term::Seq { fst, snd } => {
            collect_foreign(fst, out);
            collect_foreign(snd, out);
        }
        Term::First { inner } => {
            collect_foreign(inner, out);
        }
        Term::Choice { l, r } => {
            collect_foreign(l, out);
            collect_foreign(r, out);
        }
        Term::Loop { body } => {
            collect_foreign(body, out);
        }
        Term::App { callee, args } => {
            collect_foreign(callee, out);
            for a in args {
                collect_foreign(a, out);
            }
        }
        Term::Handle { body, impl_, .. } => {
            collect_foreign(body, out);
            collect_foreign(impl_, out);
        }
        Term::Rewrite { source, target, .. } => {
            collect_foreign(source, out);
            collect_foreign(target, out);
        }
        Term::Arr { .. } => {}
        Term::Iter {
            fuel,
            predicate,
            step,
            initial,
        } => {
            collect_foreign(fuel, out);
            collect_foreign(predicate, out);
            collect_foreign(step, out);
            collect_foreign(initial, out);
        }
        Term::Child { .. } => {}
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
    use crate::term::Term;
    use serde_json::Value;

    #[test]
    fn foreign_names_collects_recursively() {
        let s = Term::Choice {
            l: Box::new(Term::Op {
                name: "fs.read".into(),
                args: vec![Term::arr_foreign("fs.open", vec![])],
                source: ArrSource::Foreign("fs.read".into()),
                lit: None,
            }),
            r: Box::new(Term::App {
                callee: Box::new(Term::arr_foreign("net.send", vec![])),
                args: vec![Term::arr_native("id", vec![])],
            }),
        };
        let names = foreign_names(&s);
        assert!(names.contains("fs.read"));
        assert!(names.contains("fs.open"));
        assert!(names.contains("net.send"));
        assert_eq!(names.len(), 3);
    }

    #[test]
    fn no_foreign_returns_empty() {
        let s = Term::arr_native("add", vec![Term::arr_native("id", vec![])]);
        assert!(foreign_names(&s).is_empty());
    }

    #[test]
    fn capabilities_combines_foreign_and_declared() {
        let mut lang = Language::new();
        lang.eval
            .merge(EvalSchemeDef::new(
                "eval.io",
                "io",
                Term::arr_foreign(
                    "fs.read",
                    vec![Term::arr_native_lit(
                        "proj_child",
                        vec![],
                        Value::from(0u64),
                    )],
                ),
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
                Term::arr_native(
                    "add",
                    vec![
                        Term::arr_native_lit("proj_child", vec![], Value::from(0u64)),
                        Term::arr_native_lit("proj_child", vec![], Value::from(1u64)),
                    ],
                ),
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
        let s = Term::Seq {
            fst: Box::new(Term::Loop {
                body: Box::new(Term::arr_foreign("fs.read", vec![])),
            }),
            snd: Box::new(Term::First {
                inner: Box::new(Term::arr_foreign("net.send", vec![])),
            }),
        };
        let names = foreign_names(&s);
        assert!(names.contains("fs.read"));
        assert!(names.contains("net.send"));
        assert_eq!(names.len(), 2);
    }
}
