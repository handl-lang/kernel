//! Capability set derivation (ADR-0044 §7 safety).
//!
//! A `Language`'s capability set is the transitive closure of `Foreign` names
//! across all its eval schemes, plus any explicitly declared capabilities.
//! This makes "does this `Language` touch the filesystem?" a static data
//! query — no runtime sandbox required for a pure `Language`.

use std::collections::BTreeSet;

use crate::fragment::Fragment;
use crate::language::Language;
use crate::scheme::Scheme;

/// Recursively walk a [`Scheme`] and collect every `Foreign(name)` name.
pub fn foreign_names(scheme: &Scheme) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    collect_foreign(scheme, &mut out);
    out
}

fn collect_foreign(scheme: &Scheme, out: &mut BTreeSet<String>) {
    match scheme {
        Scheme::Lit(_) | Scheme::Var(_) | Scheme::Child(_) => {}
        Scheme::Bind { value, body, .. } => {
            collect_foreign(value, out);
            collect_foreign(body, out);
        }
        Scheme::App { callee, args } => {
            collect_foreign(callee, out);
            for a in args {
                collect_foreign(a, out);
            }
        }
        Scheme::Branch {
            cond, then_, else_, ..
        } => {
            collect_foreign(cond, out);
            collect_foreign(then_, out);
            collect_foreign(else_, out);
        }
        Scheme::Prim { args, .. } => {
            for a in args {
                collect_foreign(a, out);
            }
        }
        Scheme::Foreign { name, args } => {
            out.insert(name.clone());
            for a in args {
                collect_foreign(a, out);
            }
        }
        Scheme::Vau { body, .. } => {
            collect_foreign(body, out);
        }
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
    use crate::ast::AstRef;
    use crate::fragments::{CapabilityDecl, EvalSchemeDef};
    use crate::language::Language;
    use crate::scheme::Scheme;
    use serde_json::Value;

    #[test]
    fn foreign_names_collects_recursively() {
        let s = Scheme::Branch {
            cond: Box::new(Scheme::Foreign {
                name: "fs.read".into(),
                args: vec![Scheme::Foreign {
                    name: "fs.open".into(),
                    args: vec![],
                }],
            }),
            then_: Box::new(Scheme::App {
                callee: Box::new(Scheme::Foreign {
                    name: "net.send".into(),
                    args: vec![],
                }),
                args: vec![Scheme::lit(1)],
            }),
            else_: Box::new(Scheme::Child(AstRef::new(0))),
        };
        let names = foreign_names(&s);
        assert!(names.contains("fs.read"));
        assert!(names.contains("fs.open"));
        assert!(names.contains("net.send"));
        assert_eq!(names.len(), 3);
    }

    #[test]
    fn no_foreign_returns_empty() {
        let s = Scheme::Prim {
            op: "add".into(),
            args: vec![Scheme::child(0), Scheme::child(1)],
        };
        assert!(foreign_names(&s).is_empty());
    }

    #[test]
    fn capabilities_combines_foreign_and_declared() {
        let mut lang = Language::new();
        lang.eval
            .merge(EvalSchemeDef::new(
                "eval.io",
                "io",
                Scheme::foreign("fs.read", vec![Scheme::child(0)]),
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
                Scheme::prim("add", vec![Scheme::child(0), Scheme::child(1)]),
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
    fn lit_var_child_have_no_foreign() {
        assert!(foreign_names(&Scheme::lit(Value::Null)).is_empty());
        assert!(foreign_names(&Scheme::var("x")).is_empty());
        assert!(foreign_names(&Scheme::child(0)).is_empty());
    }

    #[test]
    fn bind_branch_collects_foreign() {
        let s = Scheme::Bind {
            name: "x".into(),
            value: Box::new(Scheme::Foreign {
                name: "fs.write".into(),
                args: vec![],
            }),
            body: Box::new(Scheme::Foreign {
                name: "fs.read".into(),
                args: vec![],
            }),
        };
        let names = foreign_names(&s);
        assert!(names.contains("fs.write"));
        assert!(names.contains("fs.read"));
    }
}
