//! Proof verdicts for the partial-evaluator typechecker (ADR-0068).
//!
//! The outcome of checking a type-position proposition. The typechecker is a
//! partial evaluator with a termination guard: to verify `x: T = e`, it
//! normalizes `T(e)`.
//!
//! - [`Verdict::Proven`]: normalization succeeded and the equality holds —
//!   the annotation is accepted statically.
//! - [`Verdict::Disproved`]: normalization succeeded and the equality is
//!   false — the annotation is rejected.
//! - [`Verdict::Blocked`]: normalization could not finish (a symbolic value
//!   it cannot reduce, an effect, a termination-guard budget exhausted). Per
//!   ADR-0068 the caller should accept the annotation with a runtime backstop
//!   `assert T(e)` rather than reject it.
//!
//! This is the "graduated guarantees" switch: static proof where the checker
//! can normalize, runtime fallback where it cannot.

use std::fmt;

/// The outcome of checking a type-position proposition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// Normalization succeeded and the equality holds — accept statically.
    Proven,
    /// Normalization succeeded and the equality is false — reject.
    Disproved,
    /// Normalization could not finish — accept with a runtime backstop.
    Blocked,
}

impl fmt::Display for Verdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Verdict::Proven => write!(f, "proven"),
            Verdict::Disproved => write!(f, "disproved"),
            Verdict::Blocked => write!(f, "blocked (runtime fallback)"),
        }
    }
}

/// A proof result: a verdict plus a human-readable explanation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Proof {
    /// The verdict.
    pub verdict: Verdict,
    /// Human-readable explanation.
    pub reason: String,
}

impl Proof {
    /// Construct a `Proven` proof.
    pub fn ok(reason: impl Into<String>) -> Self {
        Proof {
            verdict: Verdict::Proven,
            reason: reason.into(),
        }
    }

    /// Construct a `Disproved` proof.
    pub fn no(reason: impl Into<String>) -> Self {
        Proof {
            verdict: Verdict::Disproved,
            reason: reason.into(),
        }
    }

    /// Construct a `Blocked` proof.
    pub fn blocked(reason: impl Into<String>) -> Self {
        Proof {
            verdict: Verdict::Blocked,
            reason: reason.into(),
        }
    }
}
