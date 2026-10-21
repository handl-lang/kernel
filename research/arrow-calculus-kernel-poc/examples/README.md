# examples

Multi-file arrow programs demonstrating imports, exports, re-exports, and
aliases per ADR-0069. Each program is a composition of file-arrows via
projection and application. Run `cargo run --bin examples_check` to verify
that every `.hnl` file parses, round-trips, and that its import graph
resolves on disk.
