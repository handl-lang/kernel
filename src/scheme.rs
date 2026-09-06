//! The arrow-calculus `Scheme` kernel (ADR-0052).
//!
//! `Scheme` is the arrow-calculus evaluation kernel: the six arrow
//! primitives — `arr`, `>>>` (`Seq`), `first`, `Choice`, `Loop`, and `app`
//! — plus an `ArrSource` discipline on `arr` that keeps the capability
//! boundary structural. A `Scheme` is an engine-agnostic description of
//! *what* to evaluate for a given AST node kind, not *how*. Engines
//! (tree-walk, bytecode, cranelift) interpret schemes; the scheme itself is
//! pure data. Surface constructs are expressed as [`DesugarRule`]s, not new
//! variants.
//!
//! `Value` here is [`serde_json::Value`] — no new value type is invented.
//!
//! # The `lit` payload
//!
//! `Arr::args` is `Vec<Scheme>` — a literal value is not a sub-scheme. Literal
//! operands (the value of a `const`, the name of a `proj_env`, the index of a
//! `proj_child`) ride on `Arr`'s optional `lit: Option<Value>` payload, while
//! `args` stays a pure list of sub-schemes. The field serializes only when
//! present (`skip_serializing_if = "Option::is_none"`, `default`), so
//! foreign/prim arrows without a literal payload round-trip cleanly.

use serde::{Deserialize, Serialize};
use serde_json::Value;

/// The arrow-calculus kernel: six primitives as data (ADR-0052).
///
/// Mirrors the ADR-0052 §"Kernel representation" enum. Arrows are
/// first-class computational descriptions; handlers provide
/// interpretations of those descriptions. Every variant *constructs* a
/// new arrow description; none *execute*.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum Scheme {
    /// `arr f` — lift a named pure function over the arrow's input.
    ///
    /// Sub-schemes feed the function's arguments. Replaces the former v1
    /// `Lit`, `Var`, `Child`, `Prim`, `Foreign`. `arr` describes a pure
    /// step; interpretation is the handler's job. The `lit` payload
    /// carries an inline literal operand for ops like `const` (the
    /// value), `proj_env` (the name string), and `proj_child` (the index
    /// number); it is `None` for ordinary pure/foreign ops whose operands
    /// are sub-schemes.
    Arr {
        /// The operator name (e.g. `"add"`, `"const"`, `"proj_env"`).
        op: String,
        /// The argument sub-schemes feeding the op.
        args: Vec<Scheme>,
        /// Whether this is a native pure op or a foreign (host) call.
        source: ArrSource,
        /// An inline literal operand for ops that take a literal value
        /// rather than a sub-scheme (`const`, `proj_env`, `proj_child`).
        /// `None` for ordinary ops. Literal operands ride here so `args`
        /// stays a pure list of sub-schemes.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        lit: Option<Value>,
    },

    /// `>>>` — sequential composition.
    ///
    /// Constructs a new arrow whose output of `fst` feeds `snd`. This
    /// *composes* arrows; it does **not execute** them. The composed
    /// arrow is a description; a handler interprets it.
    Seq {
        /// The first arrow; its output feeds `snd`.
        fst: Box<Scheme>,
        /// The second arrow; fed by `fst`'s output.
        snd: Box<Scheme>,
    },

    /// `first` — fan-out: run `inner` on the first component of a pair,
    /// carry the second component through unchanged.
    ///
    /// Constructs a new arrow; does not execute.
    First {
        /// The arrow to run on the first component.
        inner: Box<Scheme>,
    },

    /// `ArrowChoice` — route on `Either`: `l` handles `Left`, `r` handles
    /// `Right`.
    ///
    /// Constructs a routing arrow; does not execute.
    Choice {
        /// The arrow handling the `Left` case.
        l: Box<Scheme>,
        /// The arrow handling the `Right` case.
        r: Box<Scheme>,
    },

    /// `ArrowLoop` — feedback (NOT iteration).
    ///
    /// `body` has shape `(In, State) ~> (Out, State)`; `Loop` hides
    /// `State` in a feedback channel, exposing `In ~> Out`. Recursion,
    /// `while`, `for`, state machines are derived patterns over `Loop`
    /// + `Choice`. The feedback semantics (causal/strict vs
    /// lazy/fixpoint) are specified separately — `Loop` in the kernel is
    /// the *description* of a feedback channel; the interpretation
    /// strategy is the handler's concern.
    Loop {
        /// The feedback body: `(In, State) ~> (Out, State)`.
        body: Box<Scheme>,
    },

    /// `app` / `ArrowApply` — dynamic/higher-order arrow application.
    ///
    /// Given `f : A ~> B` and `x : A`, `app(f, x)` invokes `f` on `x`.
    /// Required for higher-order arrows (an arrow received as runtime
    /// data). Distinct from external interpretation: `app` is a calculus
    /// operation *within* an arrow; `handle H program` interprets an
    /// entire arrow from outside.
    App {
        /// The callee arrow.
        callee: Box<Scheme>,
        /// The argument arrows.
        args: Vec<Scheme>,
    },

    /// `handle body with target = impl_` (ADR-0076): declares that `target`
    /// is a managed capability, with `body` as the handler body and `impl_`
    /// as the handler implementation. Eliminated at compile time by
    /// [`Scheme::eliminate_handlers`].
    Handle {
        /// The handler body — the program being handled. Bare `arr(target)`
        /// references within it are replaced by `impl_` during elimination.
        body: Box<Scheme>,
        /// The capability name being managed (the handle target).
        target: String,
        /// The handler implementation substituted for bare `arr(target)`
        /// references during elimination.
        impl_: Box<Scheme>,
    },
}

/// Whether an `Arr` op is a native pure function or a foreign host call.
///
/// `Foreign(name)` keeps the capability boundary structural: the
/// typechecker and load-time capability audit match on `source`, not on
/// a string prefix.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum ArrSource {
    /// A native pure op (`add`, `proj_env`, `const`, `id`, …).
    Native,
    /// A foreign (host) function call — capability-tracked. The `name` is
    /// the registered host-function name (e.g. `"fs.read"`).
    Foreign(String),
    /// A typecheck judgment op (ADR-0054 §1, §2). The op name is a
    /// judgment op (`synth_child`, `check_child`, `unify`, `extend`,
    /// `fresh_meta`, `solve_meta`, `lookup`, `quote`, `normalize`,
    /// `construct`, `match_type`). Judgment ops are interpreted by the
    /// typecheck engine, not the eval engines.
    Judgment,
    /// A dynamic host dispatch op (ADR-0060). The actual host function name
    /// is not known at scheme-construction time — it arrives as a runtime
    /// value (e.g. a string callee in a `call` node). The op name is the
    /// dispatch primitive (e.g. `call_host`); the actual host function name
    /// is a sub-scheme argument evaluated at runtime. Capability tracking
    /// for dynamic calls is handled by the engine at the call site, not by
    /// static `source` inspection.
    DynamicForeign,
}

impl Scheme {
    /// Convenience constructor for a native `arr` with no literal payload.
    pub fn arr_native(op: impl Into<String>, args: Vec<Scheme>) -> Self {
        Scheme::Arr {
            op: op.into(),
            args,
            source: ArrSource::Native,
            lit: None,
        }
    }

    /// Convenience constructor for a foreign `arr`.
    ///
    /// The host function `name` is used both as the op and as the
    /// `Foreign(name)` source, matching ADR-0052's lowering of
    /// `Foreign { name, args }`.
    pub fn arr_foreign(name: impl Into<String>, args: Vec<Scheme>) -> Self {
        let name = name.into();
        Scheme::Arr {
            op: name.clone(),
            args,
            source: ArrSource::Foreign(name),
            lit: None,
        }
    }

    /// Convenience constructor for a native `arr` carrying a literal
    /// payload (e.g. `const`, `proj_env`, `proj_child`).
    pub fn arr_native_lit(op: impl Into<String>, args: Vec<Scheme>, lit: impl Into<Value>) -> Self {
        Scheme::Arr {
            op: op.into(),
            args,
            source: ArrSource::Native,
            lit: Some(lit.into()),
        }
    }

    /// Convenience constructor for a typecheck judgment `arr` (ADR-0054
    /// §1, §2) with no literal payload.
    pub fn arr_judgment(op: impl Into<String>, args: Vec<Scheme>) -> Self {
        Scheme::Arr {
            op: op.into(),
            args,
            source: ArrSource::Judgment,
            lit: None,
        }
    }

    /// Convenience constructor for a typecheck judgment `arr` (ADR-0054
    /// §1, §2) carrying a literal payload.
    pub fn arr_judgment_lit(
        op: impl Into<String>,
        args: Vec<Scheme>,
        lit: impl Into<Value>,
    ) -> Self {
        Scheme::Arr {
            op: op.into(),
            args,
            source: ArrSource::Judgment,
            lit: Some(lit.into()),
        }
    }

    /// Convenience constructor for `>>>` (sequential composition).
    pub fn seq(fst: Scheme, snd: Scheme) -> Self {
        Scheme::Seq {
            fst: Box::new(fst),
            snd: Box::new(snd),
        }
    }

    /// Convenience constructor for `first` (fan-out on the first
    /// component of a pair).
    pub fn first(inner: Scheme) -> Self {
        Scheme::First {
            inner: Box::new(inner),
        }
    }

    /// Convenience constructor for `ArrowChoice` routing.
    pub fn choice(l: Scheme, r: Scheme) -> Self {
        Scheme::Choice {
            l: Box::new(l),
            r: Box::new(r),
        }
    }

    /// Convenience constructor for `ArrowLoop` feedback.
    ///
    /// Named `loop_feedback` rather than `loop` (a reserved word) to keep
    /// the constructor name clear and non-raw.
    pub fn loop_feedback(body: Scheme) -> Self {
        Scheme::Loop {
            body: Box::new(body),
        }
    }

    /// Convenience constructor for `app` / `ArrowApply` (dynamic
    /// higher-order arrow application).
    pub fn app(callee: Scheme, args: Vec<Scheme>) -> Self {
        Scheme::App {
            callee: Box::new(callee),
            args,
        }
    }

    /// Construct a `handle body with target = impl_` node (ADR-0076).
    pub fn handle(body: Scheme, target: impl Into<String>, impl_: Scheme) -> Self {
        Scheme::Handle {
            body: Box::new(body),
            target: target.into(),
            impl_: Box::new(impl_),
        }
    }

    /// Eliminate every [`Scheme::Handle`] node in this scheme (ADR-0076).
    ///
    /// For each `handle body with target = impl_`:
    /// 1. Recursively eliminate handlers in `body` and `impl_`.
    /// 2. Substitute bare `arr(target)` references in the eliminated body
    ///    with the eliminated impl.
    /// 3. Return the substituted body.
    pub fn eliminate_handlers(&self) -> Scheme {
        match self {
            Scheme::Arr {
                op,
                args,
                source,
                lit,
            } => {
                let new_args: Vec<Scheme> = args.iter().map(|a| a.eliminate_handlers()).collect();
                Scheme::Arr {
                    op: op.clone(),
                    args: new_args,
                    source: source.clone(),
                    lit: lit.clone(),
                }
            }
            Scheme::Seq { fst, snd } => Scheme::Seq {
                fst: Box::new(fst.eliminate_handlers()),
                snd: Box::new(snd.eliminate_handlers()),
            },
            Scheme::First { inner } => Scheme::First {
                inner: Box::new(inner.eliminate_handlers()),
            },
            Scheme::Choice { l, r } => Scheme::Choice {
                l: Box::new(l.eliminate_handlers()),
                r: Box::new(r.eliminate_handlers()),
            },
            Scheme::Loop { body } => Scheme::Loop {
                body: Box::new(body.eliminate_handlers()),
            },
            Scheme::App { callee, args } => {
                let new_args: Vec<Scheme> = args.iter().map(|a| a.eliminate_handlers()).collect();
                Scheme::App {
                    callee: Box::new(callee.eliminate_handlers()),
                    args: new_args,
                }
            }
            Scheme::Handle {
                body,
                target,
                impl_,
            } => {
                let elim_body = body.eliminate_handlers();
                let elim_impl = impl_.eliminate_handlers();
                substitute_capability(&elim_body, target, &elim_impl)
            }
        }
    }
}

/// Substitute bare `arr(target)` references in `scheme` with `impl_`.
///
/// A bare `arr(target)` reference is an `Arr` node whose `op` equals `target`,
/// with no sub-scheme arguments and no literal payload. Such a reference may
/// carry either a [`ArrSource::Native`] source (the common case, as produced
/// by `arr_native`) or a [`ArrSource::Foreign`] source naming `target`. Both
/// are recognized and replaced by `impl_`. All other nodes are recursed into
/// structurally.
fn substitute_capability(scheme: &Scheme, target: &str, impl_: &Scheme) -> Scheme {
    match scheme {
        Scheme::Arr {
            op,
            args,
            source,
            lit,
        } => {
            // Check if this is a bare `arr(target)` reference:
            // op == target, no args, no lit. The source may be Native (the
            // common case from `arr_native`) or Foreign(target).
            if op == target && args.is_empty() && lit.is_none() {
                match source {
                    ArrSource::Native => return impl_.clone(),
                    ArrSource::Foreign(name) if name == target => return impl_.clone(),
                    _ => {}
                }
            }
            // Otherwise, recurse into args.
            let new_args: Vec<Scheme> = args
                .iter()
                .map(|a| substitute_capability(a, target, impl_))
                .collect();
            Scheme::Arr {
                op: op.clone(),
                args: new_args,
                source: source.clone(),
                lit: lit.clone(),
            }
        }
        Scheme::Seq { fst, snd } => Scheme::Seq {
            fst: Box::new(substitute_capability(fst, target, impl_)),
            snd: Box::new(substitute_capability(snd, target, impl_)),
        },
        Scheme::First { inner } => Scheme::First {
            inner: Box::new(substitute_capability(inner, target, impl_)),
        },
        Scheme::Choice { l, r } => Scheme::Choice {
            l: Box::new(substitute_capability(l, target, impl_)),
            r: Box::new(substitute_capability(r, target, impl_)),
        },
        Scheme::Loop { body } => Scheme::Loop {
            body: Box::new(substitute_capability(body, target, impl_)),
        },
        Scheme::App { callee, args } => {
            let new_args: Vec<Scheme> = args
                .iter()
                .map(|a| substitute_capability(a, target, impl_))
                .collect();
            Scheme::App {
                callee: Box::new(substitute_capability(callee, target, impl_)),
                args: new_args,
            }
        }
        Scheme::Handle {
            body,
            target: t,
            impl_: i,
        } => {
            // Nested handle — should not occur after elimination, but handle
            // it by recursing into both children.
            Scheme::Handle {
                body: Box::new(substitute_capability(body, target, impl_)),
                target: t.clone(),
                impl_: Box::new(substitute_capability(i, target, impl_)),
            }
        }
    }
}

/// Eliminate all handlers in a scheme (free function version).
pub fn eliminate_all_handlers(scheme: &Scheme) -> Scheme {
    scheme.eliminate_handlers()
}

/// Eliminate handlers in a scheme (alias for compatibility).
pub fn eliminate_handler_in_scheme(scheme: &Scheme) -> Scheme {
    scheme.eliminate_handlers()
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::Value;

    fn roundtrip(s: &Scheme) -> Scheme {
        let j = serde_json::to_string(s).unwrap();
        serde_json::from_str(&j).unwrap()
    }

    #[test]
    fn arr_native_constructs_and_roundtrips() {
        let s = Scheme::arr_native("add", vec![Scheme::arr_native_lit("proj_child", vec![], 0)]);
        assert_eq!(s, roundtrip(&s));
        let j = serde_json::to_string(&s).unwrap();
        assert!(j.contains("\"Arr\""));
        assert!(j.contains("\"Native\""));
        // The outer arr has no lit; the inner proj_child does.
        match s {
            Scheme::Arr { lit, .. } => assert_eq!(lit, None),
            other => panic!("expected Arr, got {other:?}"),
        }
    }

    #[test]
    fn arr_foreign_constructs_and_roundtrips() {
        let s = Scheme::arr_foreign(
            "fs.read",
            vec![Scheme::arr_native_lit("proj_child", vec![], 0)],
        );
        assert_eq!(s, roundtrip(&s));
        let j = serde_json::to_string(&s).unwrap();
        assert!(j.contains("\"Foreign\""));
        assert!(j.contains("\"fs.read\""));
    }

    #[test]
    fn arr_lit_present_roundtrips() {
        let s = Scheme::arr_native_lit("const", vec![], Value::from(42));
        assert_eq!(s, roundtrip(&s));
        let j = serde_json::to_string(&s).unwrap();
        assert!(j.contains("\"lit\""));
        assert!(j.contains("42"));
    }

    #[test]
    fn arr_lit_absent_omitted() {
        let s = Scheme::arr_native("id", vec![]);
        let j = serde_json::to_string(&s).unwrap();
        assert!(!j.contains("\"lit\""));
        assert_eq!(s, roundtrip(&s));
    }

    #[test]
    fn seq_constructs_and_roundtrips() {
        let s = Scheme::seq(
            Scheme::arr_native("id", vec![]),
            Scheme::arr_native("id", vec![]),
        );
        assert_eq!(s, roundtrip(&s));
        let j = serde_json::to_string(&s).unwrap();
        assert!(j.contains("\"Seq\""));
    }

    #[test]
    fn first_constructs_and_roundtrips() {
        let s = Scheme::first(Scheme::arr_native("id", vec![]));
        assert_eq!(s, roundtrip(&s));
        let j = serde_json::to_string(&s).unwrap();
        assert!(j.contains("\"First\""));
    }

    #[test]
    fn choice_constructs_and_roundtrips() {
        let s = Scheme::choice(
            Scheme::arr_native("id", vec![]),
            Scheme::arr_native("id", vec![]),
        );
        assert_eq!(s, roundtrip(&s));
        let j = serde_json::to_string(&s).unwrap();
        assert!(j.contains("\"Choice\""));
        assert!(j.contains("\"l\""));
        assert!(j.contains("\"r\""));
    }

    #[test]
    fn loop_feedback_constructs_and_roundtrips() {
        let s = Scheme::loop_feedback(Scheme::arr_native("id", vec![]));
        assert_eq!(s, roundtrip(&s));
        let j = serde_json::to_string(&s).unwrap();
        assert!(j.contains("\"Loop\""));
    }

    #[test]
    fn app_constructs_and_roundtrips() {
        let s = Scheme::app(
            Scheme::arr_native_lit("proj_env", vec![], "f"),
            vec![Scheme::arr_native_lit("const", vec![], 1)],
        );
        assert_eq!(s, roundtrip(&s));
        let j = serde_json::to_string(&s).unwrap();
        assert!(j.contains("\"App\""));
    }

    #[test]
    fn arr_source_native_roundtrips() {
        let src = ArrSource::Native;
        let j = serde_json::to_string(&src).unwrap();
        assert_eq!(j, "\"Native\"");
        let back: ArrSource = serde_json::from_str(&j).unwrap();
        assert_eq!(src, back);
    }

    #[test]
    fn arr_source_foreign_roundtrips() {
        let src = ArrSource::Foreign("fs.read".into());
        let j = serde_json::to_string(&src).unwrap();
        assert!(j.contains("\"Foreign\""));
        let back: ArrSource = serde_json::from_str(&j).unwrap();
        assert_eq!(src, back);
    }

    #[test]
    fn nested_scheme_roundtrips() {
        let s = Scheme::seq(
            Scheme::arr_native("id", vec![]),
            Scheme::choice(
                Scheme::loop_feedback(Scheme::arr_foreign("fs.read", vec![])),
                Scheme::app(
                    Scheme::arr_native_lit("proj_env", vec![], "f"),
                    vec![Scheme::arr_native_lit("const", vec![], Value::Bool(true))],
                ),
            ),
        );
        assert_eq!(s, roundtrip(&s));
    }
}
