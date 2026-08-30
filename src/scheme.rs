//! The `Scheme` combinator set — the eval equivalent of grammar rows.
//!
//! A `Scheme` is an engine-agnostic description of *what* to evaluate for a
//! given AST node kind, not *how*. Engines (tree-walk, bytecode, cranelift)
//! interpret schemes; the scheme itself is pure data. The combinator set is
//! deliberately small (8 variants, see ADR-0044 §4): surface constructs are
//! expressed as [`DesugarRule`]s, not new variants.
//!
//! `Value` here is [`serde_json::Value`] — no new value type is invented.

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::ast::AstRef;

/// A semantic combinator describing how to evaluate a node kind.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum Scheme {
    /// A literal value.
    Lit(Value),
    /// A variable reference by name.
    Var(String),
    /// Evaluate the child at the given arena index.
    Child(AstRef),
    /// Bind a name to a value within a body.
    Bind {
        /// The name to bind.
        name: String,
        /// The value to bind.
        value: Box<Scheme>,
        /// The body evaluated in the extended scope.
        body: Box<Scheme>,
    },
    /// Apply a callee to arguments.
    App {
        /// The function/callee scheme.
        callee: Box<Scheme>,
        /// The argument schemes.
        args: Vec<Scheme>,
    },
    /// Conditional branching.
    Branch {
        /// The condition.
        cond: Box<Scheme>,
        /// The then-branch.
        #[serde(rename = "then")]
        then_: Box<Scheme>,
        /// The else-branch.
        else_: Box<Scheme>,
    },
    /// A primitive operation.
    Prim {
        /// The primitive operator name (e.g. `"add"`).
        op: String,
        /// The argument schemes.
        args: Vec<Scheme>,
    },
    /// A foreign (host) function call — capability-tracked.
    Foreign {
        /// The registered host function name.
        name: String,
        /// The argument schemes.
        args: Vec<Scheme>,
    },
}

impl Scheme {
    /// Convenience constructor for a literal.
    pub fn lit(value: impl Into<Value>) -> Self {
        Scheme::Lit(value.into())
    }

    /// Convenience constructor for a variable.
    pub fn var(name: impl Into<String>) -> Self {
        Scheme::Var(name.into())
    }

    /// Convenience constructor for a child reference.
    pub fn child(idx: usize) -> Self {
        Scheme::Child(AstRef::new(idx))
    }

    /// Convenience constructor for a primitive.
    pub fn prim(op: impl Into<String>, args: Vec<Scheme>) -> Self {
        Scheme::Prim {
            op: op.into(),
            args,
        }
    }

    /// Convenience constructor for a foreign call.
    pub fn foreign(name: impl Into<String>, args: Vec<Scheme>) -> Self {
        Scheme::Foreign {
            name: name.into(),
            args,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn roundtrip(s: &Scheme) -> Scheme {
        let j = serde_json::to_string(s).unwrap();
        serde_json::from_str(&j).unwrap()
    }

    #[test]
    fn lit_constructs_and_roundtrips() {
        let s = Scheme::lit(42);
        assert_eq!(s, roundtrip(&s));
        assert_eq!(s, Scheme::Lit(Value::from(42)));
    }

    #[test]
    fn var_constructs_and_roundtrips() {
        let s = Scheme::var("x");
        assert_eq!(s, roundtrip(&s));
    }

    #[test]
    fn child_constructs_and_roundtrips() {
        let s = Scheme::child(3);
        assert_eq!(s, roundtrip(&s));
        assert_eq!(s, Scheme::Child(AstRef::new(3)));
    }

    #[test]
    fn bind_constructs_and_roundtrips() {
        let s = Scheme::Bind {
            name: "x".into(),
            value: Box::new(Scheme::lit(1)),
            body: Box::new(Scheme::var("x")),
        };
        assert_eq!(s, roundtrip(&s));
    }

    #[test]
    fn app_constructs_and_roundtrips() {
        let s = Scheme::App {
            callee: Box::new(Scheme::var("f")),
            args: vec![Scheme::lit(1), Scheme::lit(2)],
        };
        assert_eq!(s, roundtrip(&s));
    }

    #[test]
    fn branch_constructs_and_roundtrips() {
        let s = Scheme::Branch {
            cond: Box::new(Scheme::var("c")),
            then_: Box::new(Scheme::lit(1)),
            else_: Box::new(Scheme::lit(2)),
        };
        let back = roundtrip(&s);
        assert_eq!(s, back);
        // Verify the serde rename to "then".
        let j = serde_json::to_string(&s).unwrap();
        assert!(j.contains("\"then\""));
    }

    #[test]
    fn prim_constructs_and_roundtrips() {
        let s = Scheme::prim(
            "add",
            vec![Scheme::child(0), Scheme::child(1)],
        );
        assert_eq!(s, roundtrip(&s));
    }

    #[test]
    fn foreign_constructs_and_roundtrips() {
        let s = Scheme::foreign("print", vec![Scheme::child(0)]);
        assert_eq!(s, roundtrip(&s));
    }

    #[test]
    fn nested_scheme_roundtrips() {
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
        assert_eq!(s, roundtrip(&s));
    }
}
