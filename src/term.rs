//! Re-export of the arrow-calculus `Term` kernel from `plugin-engine`.

pub use plugin_engine::{
    ArrSource, RewriteWitness, Term, eliminate_all_handlers, eliminate_handler_in_scheme,
};
