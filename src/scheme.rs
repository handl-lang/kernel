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
    pub fn arr_native_lit(
        op: impl Into<String>,
        args: Vec<Scheme>,
        lit: impl Into<Value>,
    ) -> Self {
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
        let s = Scheme::arr_foreign("fs.read", vec![Scheme::arr_native_lit("proj_child", vec![], 0)]);
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
        let s = Scheme::seq(Scheme::arr_native("id", vec![]), Scheme::arr_native("id", vec![]));
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
        let s = Scheme::choice(Scheme::arr_native("id", vec![]), Scheme::arr_native("id", vec![]));
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
