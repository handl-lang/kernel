//! The v2 arrow-calculus `SchemeV2` kernel (ADR-0052).
//!
//! `SchemeV2` is the arrow-calculus replacement for the v1 [`Scheme`]
//! combinator set. Where v1 enumerated eight evaluation combinators
//! (`Lit`/`Var`/`Child`/`Bind`/`App`/`Branch`/`Prim`/`Foreign`/`Vau`),
//! the v2 kernel is the six arrow-calculus primitives — `arr`, `>>>`
//! (`Seq`), `first`, `Choice`, `Loop`, and `app` — plus an `ArrSource`
//! discipline on `arr` that keeps the capability boundary structural.
//!
//! This is an **additive** module: the v1 [`Scheme`] enum is untouched and
//! remains the canonical representation for v1 `Language` values. A v2
//! engine accepts v1 languages backward-compatibly (see
//! [`crate::version::SchemeVersion`]); the reverse is a compile-time
//! error. Use [`lower_v1_to_v2`] to translate a v1 scheme into the v2
//! kernel.
//!
//! `Value` here is [`serde_json::Value`] — no new value type is invented.
//!
//! # The `lit` payload
//!
//! The ADR-0052 lowering table sketches `Lit(v)` as
//! `Arr { op: "const", args: [v] }`, where `v` is a JSON value, not a
//! `SchemeV2`. But `Arr::args` is `Vec<SchemeV2>` — a literal value is
//! not a sub-scheme. The ADR's `args: [v]` is loose sketch notation.
//! This module concretizes it faithfully and minimally by giving `Arr`
//! an optional `lit: Option<Value>` payload: literal operands (the value
//! of a `const`, the name of a `proj_env`, the index of a `proj_child`)
//! ride on `lit`, while `args` stays a pure list of sub-schemes. The
//! field serializes only when present
//! (`skip_serializing_if = "Option::is_none"`, `default`), so
//! foreign/prim arrows without a literal payload round-trip cleanly.

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::error::LangError;
use crate::scheme::Scheme;

/// The v2 arrow-calculus kernel: six primitives as data (ADR-0052).
///
/// Mirrors the ADR-0052 §"Kernel representation" enum. Arrows are
/// first-class computational descriptions; handlers provide
/// interpretations of those descriptions. Every variant *constructs* a
/// new arrow description; none *execute*.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum SchemeV2 {
    /// `arr f` — lift a named pure function over the arrow's input.
    ///
    /// Sub-schemes feed the function's arguments. Replaces `Lit`, `Var`,
    /// `Child`, `Prim`, `Foreign`. `arr` describes a pure step;
    /// interpretation is the handler's job. The `lit` payload carries an
    /// inline literal operand for ops like `const` (the value), `proj_env`
    /// (the name string), and `proj_child` (the index number); it is
    /// `None` for ordinary pure/foreign ops whose operands are sub-schemes.
    Arr {
        /// The operator name (e.g. `"add"`, `"const"`, `"proj_env"`).
        op: String,
        /// The argument sub-schemes feeding the op.
        args: Vec<SchemeV2>,
        /// Whether this is a native pure op or a foreign (host) call.
        source: ArrSource,
        /// An inline literal operand for ops that take a literal value
        /// rather than a sub-scheme (`const`, `proj_env`, `proj_child`).
        /// `None` for ordinary ops. This concretizes ADR-0052's lowering
        /// table, which sketched `args: [v]` loosely; literal operands
        /// ride here so `args` stays a pure list of sub-schemes.
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
        fst: Box<SchemeV2>,
        /// The second arrow; fed by `fst`'s output.
        snd: Box<SchemeV2>,
    },

    /// `first` — fan-out: run `inner` on the first component of a pair,
    /// carry the second component through unchanged.
    ///
    /// Constructs a new arrow; does not execute.
    First {
        /// The arrow to run on the first component.
        inner: Box<SchemeV2>,
    },

    /// `ArrowChoice` — route on `Either`: `l` handles `Left`, `r` handles
    /// `Right`.
    ///
    /// Replaces `Branch`. Constructs a routing arrow; does not execute.
    Choice {
        /// The arrow handling the `Left` case.
        l: Box<SchemeV2>,
        /// The arrow handling the `Right` case.
        r: Box<SchemeV2>,
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
        body: Box<SchemeV2>,
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
        callee: Box<SchemeV2>,
        /// The argument arrows.
        args: Vec<SchemeV2>,
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
}

impl SchemeV2 {
    /// Convenience constructor for a native `arr` with no literal payload.
    pub fn arr_native(op: impl Into<String>, args: Vec<SchemeV2>) -> Self {
        SchemeV2::Arr {
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
    pub fn arr_foreign(name: impl Into<String>, args: Vec<SchemeV2>) -> Self {
        let name = name.into();
        SchemeV2::Arr {
            op: name.clone(),
            args,
            source: ArrSource::Foreign(name),
            lit: None,
        }
    }

    /// Convenience constructor for a native `arr` carrying a literal
    /// payload (e.g. `const`, `proj_env`, `proj_child`).
    pub fn arr_native_lit(
        op: impl Into<String>,
        args: Vec<SchemeV2>,
        lit: impl Into<Value>,
    ) -> Self {
        SchemeV2::Arr {
            op: op.into(),
            args,
            source: ArrSource::Native,
            lit: Some(lit.into()),
        }
    }

    /// Convenience constructor for `>>>` (sequential composition).
    pub fn seq(fst: SchemeV2, snd: SchemeV2) -> Self {
        SchemeV2::Seq {
            fst: Box::new(fst),
            snd: Box::new(snd),
        }
    }

    /// Convenience constructor for `first` (fan-out on the first
    /// component of a pair).
    pub fn first(inner: SchemeV2) -> Self {
        SchemeV2::First {
            inner: Box::new(inner),
        }
    }

    /// Convenience constructor for `ArrowChoice` routing.
    pub fn choice(l: SchemeV2, r: SchemeV2) -> Self {
        SchemeV2::Choice {
            l: Box::new(l),
            r: Box::new(r),
        }
    }

    /// Convenience constructor for `ArrowLoop` feedback.
    ///
    /// Named `loop_feedback` rather than `loop` (a reserved word) to keep
    /// the constructor name clear and non-raw.
    pub fn loop_feedback(body: SchemeV2) -> Self {
        SchemeV2::Loop {
            body: Box::new(body),
        }
    }

    /// Convenience constructor for `app` / `ArrowApply` (dynamic
    /// higher-order arrow application).
    pub fn app(callee: SchemeV2, args: Vec<SchemeV2>) -> Self {
        SchemeV2::App {
            callee: Box::new(callee),
            args,
        }
    }
}

/// Lower a v1 [`Scheme`] into the v2 arrow-calculus kernel
/// (ADR-0052 §"Lowering table").
///
/// Implements the ADR's lowering table concretely, resolving the ADR's
/// loose `args: [v]` sketch by carrying literal operands on the `Arr`
/// `lit` payload (see the module-level docs).
///
/// `Vau` is removed from the v2 kernel and yields an error. The
/// static-vs-dynamic `App` distinction is a desugar-time concern;
/// `lower_v1_to_v2` conservatively emits the dynamic `app` form for
/// every v1 `App`, since v1 `App` is dynamic application and the
/// lowering has no scope information to identify a static callee.
///
/// # Errors
///
/// Returns [`LangError::Engine`] if the v1 scheme contains a `Vau`
/// combinator, which has no v2 kernel equivalent.
pub fn lower_v1_to_v2(s: &Scheme) -> Result<SchemeV2, LangError> {
    Ok(match s {
        Scheme::Lit(v) => SchemeV2::arr_native_lit("const", vec![], v.clone()),
        Scheme::Var(n) => SchemeV2::arr_native_lit("proj_env", vec![], Value::String(n.clone())),
        Scheme::Child(i) => {
            SchemeV2::arr_native_lit("proj_child", vec![], Value::from(i.index() as u64))
        }
        Scheme::Prim { op, args } => {
            let lowered: Vec<SchemeV2> = args.iter().map(lower_v1_to_v2).collect::<Result<_, _>>()?;
            SchemeV2::arr_native(op.clone(), lowered)
        }
        Scheme::Foreign { name, args } => {
            let lowered: Vec<SchemeV2> = args.iter().map(lower_v1_to_v2).collect::<Result<_, _>>()?;
            SchemeV2::arr_foreign(name.clone(), lowered)
        }
        Scheme::Bind { name, value, body } => {
            // value >>> arr (extend env with name) >>> body
            let extend = SchemeV2::arr_native_lit("extend_env", vec![], Value::String(name.clone()));
            SchemeV2::seq(
                SchemeV2::seq(lower_v1_to_v2(value)?, extend),
                lower_v1_to_v2(body)?,
            )
        }
        Scheme::App { callee, args } => {
            // Conservative default: the dynamic `app` form. The
            // static-callee (composition) desugar is a desugar-time
            // concern requiring scope info this lowering lacks.
            let lowered: Vec<SchemeV2> = args.iter().map(lower_v1_to_v2).collect::<Result<_, _>>()?;
            SchemeV2::app(lower_v1_to_v2(callee)?, lowered)
        }
        Scheme::Branch { cond, then_, else_ } => {
            // c >>> arr tag >>> Choice(t, e)
            let tag = SchemeV2::arr_native("tag", vec![]);
            SchemeV2::seq(
                SchemeV2::seq(lower_v1_to_v2(cond)?, tag),
                SchemeV2::choice(lower_v1_to_v2(then_)?, lower_v1_to_v2(else_)?),
            )
        }
        Scheme::Vau { .. } => {
            return Err(LangError::Engine(
                "lower_v1_to_v2: Vau is removed from the v2 kernel (ADR-0052); cannot lower"
                    .into(),
            ));
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::AstRef;
    use crate::scheme::Scheme;

    fn roundtrip(s: &SchemeV2) -> SchemeV2 {
        let j = serde_json::to_string(s).unwrap();
        serde_json::from_str(&j).unwrap()
    }

    #[test]
    fn arr_native_constructs_and_roundtrips() {
        let s = SchemeV2::arr_native("add", vec![SchemeV2::arr_native_lit("proj_child", vec![], 0)]);
        assert_eq!(s, roundtrip(&s));
        let j = serde_json::to_string(&s).unwrap();
        assert!(j.contains("\"Arr\""));
        assert!(j.contains("\"Native\""));
        // The outer arr has no lit; the inner proj_child does.
        match s {
            SchemeV2::Arr { lit, .. } => assert_eq!(lit, None),
            other => panic!("expected Arr, got {other:?}"),
        }
    }

    #[test]
    fn arr_foreign_constructs_and_roundtrips() {
        let s = SchemeV2::arr_foreign("fs.read", vec![SchemeV2::arr_native_lit("proj_child", vec![], 0)]);
        assert_eq!(s, roundtrip(&s));
        let j = serde_json::to_string(&s).unwrap();
        assert!(j.contains("\"Foreign\""));
        assert!(j.contains("\"fs.read\""));
    }

    #[test]
    fn arr_lit_present_roundtrips() {
        let s = SchemeV2::arr_native_lit("const", vec![], Value::from(42));
        assert_eq!(s, roundtrip(&s));
        let j = serde_json::to_string(&s).unwrap();
        assert!(j.contains("\"lit\""));
        assert!(j.contains("42"));
    }

    #[test]
    fn arr_lit_absent_omitted() {
        let s = SchemeV2::arr_native("id", vec![]);
        let j = serde_json::to_string(&s).unwrap();
        assert!(!j.contains("\"lit\""));
        assert_eq!(s, roundtrip(&s));
    }

    #[test]
    fn seq_constructs_and_roundtrips() {
        let s = SchemeV2::seq(SchemeV2::arr_native("id", vec![]), SchemeV2::arr_native("id", vec![]));
        assert_eq!(s, roundtrip(&s));
        let j = serde_json::to_string(&s).unwrap();
        assert!(j.contains("\"Seq\""));
    }

    #[test]
    fn first_constructs_and_roundtrips() {
        let s = SchemeV2::first(SchemeV2::arr_native("id", vec![]));
        assert_eq!(s, roundtrip(&s));
        let j = serde_json::to_string(&s).unwrap();
        assert!(j.contains("\"First\""));
    }

    #[test]
    fn choice_constructs_and_roundtrips() {
        let s = SchemeV2::choice(SchemeV2::arr_native("id", vec![]), SchemeV2::arr_native("id", vec![]));
        assert_eq!(s, roundtrip(&s));
        let j = serde_json::to_string(&s).unwrap();
        assert!(j.contains("\"Choice\""));
        assert!(j.contains("\"l\""));
        assert!(j.contains("\"r\""));
    }

    #[test]
    fn loop_feedback_constructs_and_roundtrips() {
        let s = SchemeV2::loop_feedback(SchemeV2::arr_native("id", vec![]));
        assert_eq!(s, roundtrip(&s));
        let j = serde_json::to_string(&s).unwrap();
        assert!(j.contains("\"Loop\""));
    }

    #[test]
    fn app_constructs_and_roundtrips() {
        let s = SchemeV2::app(
            SchemeV2::arr_native_lit("proj_env", vec![], "f"),
            vec![SchemeV2::arr_native_lit("const", vec![], 1)],
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
    fn nested_scheme_v2_roundtrips() {
        let s = SchemeV2::seq(
            SchemeV2::arr_native("id", vec![]),
            SchemeV2::choice(
                SchemeV2::loop_feedback(SchemeV2::arr_foreign("fs.read", vec![])),
                SchemeV2::app(
                    SchemeV2::arr_native_lit("proj_env", vec![], "f"),
                    vec![SchemeV2::arr_native_lit("const", vec![], Value::Bool(true))],
                ),
            ),
        );
        assert_eq!(s, roundtrip(&s));
    }

    // --- lower_v1_to_v2 tests ---

    #[test]
    fn lower_lit() {
        let s = Scheme::lit(42);
        let v2 = lower_v1_to_v2(&s).unwrap();
        match v2 {
            SchemeV2::Arr { op, source, lit, .. } => {
                assert_eq!(op, "const");
                assert_eq!(source, ArrSource::Native);
                assert_eq!(lit, Some(Value::from(42)));
            }
            other => panic!("expected Arr, got {other:?}"),
        }
    }

    #[test]
    fn lower_var() {
        let s = Scheme::var("x");
        let v2 = lower_v1_to_v2(&s).unwrap();
        match v2 {
            SchemeV2::Arr { op, lit, .. } => {
                assert_eq!(op, "proj_env");
                assert_eq!(lit, Some(Value::String("x".into())));
            }
            other => panic!("expected Arr, got {other:?}"),
        }
    }

    #[test]
    fn lower_child() {
        let s = Scheme::child(3);
        let v2 = lower_v1_to_v2(&s).unwrap();
        match v2 {
            SchemeV2::Arr { op, lit, .. } => {
                assert_eq!(op, "proj_child");
                assert_eq!(lit, Some(Value::from(3u64)));
            }
            other => panic!("expected Arr, got {other:?}"),
        }
    }

    #[test]
    fn lower_prim() {
        let s = Scheme::prim("add", vec![Scheme::child(0), Scheme::child(1)]);
        let v2 = lower_v1_to_v2(&s).unwrap();
        match v2 {
            SchemeV2::Arr { op, args, source, lit } => {
                assert_eq!(op, "add");
                assert_eq!(source, ArrSource::Native);
                assert_eq!(lit, None);
                assert_eq!(args.len(), 2);
            }
            other => panic!("expected Arr, got {other:?}"),
        }
    }

    #[test]
    fn lower_foreign() {
        let s = Scheme::foreign("fs.read", vec![Scheme::child(0)]);
        let v2 = lower_v1_to_v2(&s).unwrap();
        match v2 {
            SchemeV2::Arr { op, source, args, lit } => {
                assert_eq!(op, "fs.read");
                assert_eq!(source, ArrSource::Foreign("fs.read".into()));
                assert_eq!(lit, None);
                assert_eq!(args.len(), 1);
            }
            other => panic!("expected Arr, got {other:?}"),
        }
    }

    #[test]
    fn lower_bind() {
        let s = Scheme::Bind {
            name: "x".into(),
            value: Box::new(Scheme::lit(1)),
            body: Box::new(Scheme::var("x")),
        };
        let v2 = lower_v1_to_v2(&s).unwrap();
        // value >>> extend_env(x) >>> body
        match v2 {
            SchemeV2::Seq { fst, snd } => {
                match *fst {
                    SchemeV2::Seq { fst, snd } => {
                        assert!(matches!(*fst, SchemeV2::Arr { op, .. } if op == "const"));
                        match *snd {
                            SchemeV2::Arr { op, lit, .. } => {
                                assert_eq!(op, "extend_env");
                                assert_eq!(lit, Some(Value::String("x".into())));
                            }
                            other => panic!("expected extend_env Arr, got {other:?}"),
                        }
                    }
                    other => panic!("expected inner Seq, got {other:?}"),
                }
                assert!(matches!(*snd, SchemeV2::Arr { op, .. } if op == "proj_env"));
            }
            other => panic!("expected outer Seq, got {other:?}"),
        }
    }

    #[test]
    fn lower_app_dynamic() {
        let s = Scheme::App {
            callee: Box::new(Scheme::var("f")),
            args: vec![Scheme::lit(1)],
        };
        let v2 = lower_v1_to_v2(&s).unwrap();
        match v2 {
            SchemeV2::App { callee, args } => {
                assert!(matches!(*callee, SchemeV2::Arr { op, .. } if op == "proj_env"));
                assert_eq!(args.len(), 1);
            }
            other => panic!("expected App, got {other:?}"),
        }
    }

    #[test]
    fn lower_branch() {
        let s = Scheme::Branch {
            cond: Box::new(Scheme::var("c")),
            then_: Box::new(Scheme::lit(1)),
            else_: Box::new(Scheme::lit(2)),
        };
        let v2 = lower_v1_to_v2(&s).unwrap();
        // c >>> tag >>> Choice(t, e)
        match v2 {
            SchemeV2::Seq { fst, snd } => {
                match *fst {
                    SchemeV2::Seq { fst, snd } => {
                        assert!(matches!(*fst, SchemeV2::Arr { op, .. } if op == "proj_env"));
                        assert!(matches!(*snd, SchemeV2::Arr { op, .. } if op == "tag"));
                    }
                    other => panic!("expected inner Seq, got {other:?}"),
                }
                assert!(matches!(*snd, SchemeV2::Choice { .. }));
            }
            other => panic!("expected outer Seq, got {other:?}"),
        }
    }

    #[test]
    fn lower_vau_errors() {
        let s = Scheme::vau(vec!["a".into()], Scheme::lit(42));
        let err = lower_v1_to_v2(&s).unwrap_err();
        match err {
            LangError::Engine(msg) => assert!(msg.contains("Vau")),
            other => panic!("expected Engine error, got {other:?}"),
        }
    }

    #[test]
    fn lower_nested_roundtrips() {
        let s = Scheme::Branch {
            cond: Box::new(Scheme::Prim {
                op: "lt".into(),
                args: vec![Scheme::child(0), Scheme::lit(10)],
            }),
            then_: Box::new(Scheme::App {
                callee: Box::new(Scheme::var("f")),
                args: vec![Scheme::child(1)],
            }),
            else_: Box::new(Scheme::Foreign {
                name: "panic".into(),
                args: vec![Scheme::lit("too big")],
            }),
        };
        let v2 = lower_v1_to_v2(&s).unwrap();
        assert_eq!(v2, roundtrip(&v2));
    }

    #[test]
    fn lower_child_uses_astref_index() {
        let s = Scheme::Child(AstRef::new(7));
        let v2 = lower_v1_to_v2(&s).unwrap();
        match v2 {
            SchemeV2::Arr { lit, .. } => assert_eq!(lit, Some(Value::from(7u64))),
            other => panic!("expected Arr, got {other:?}"),
        }
    }
}
