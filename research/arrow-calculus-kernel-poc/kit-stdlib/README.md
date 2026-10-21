# kit-stdlib

Importable arrow stdlib per ADR-0069 Phase 7 ("stdlib as importable arrow files").

Each `.hnl` file is itself an arrow:

- a single-binding file is that arrow directly;
- a multi-name file (e.g. `data/atoms`) is a record arrow whose fields are the bindings.

Imports normalize to projections of the referenced file-arrow. Re-exports
(`export ... from`) compose record arrows via projection.
