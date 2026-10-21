// handl v0.1 — Examples & stdlib integrity check (ADR-0069 Phase 7)
//
// Standalone test binary in the PoC style (fn main() with PASS/FAIL). It is
// std-only (no external dependencies). It walks the `kit-stdlib/` and
// `examples/` directories recursively, and for every `.hnl` file:
//
//   1. parses it (parse) and asserts Ok;
//   2. verifies round-trip fidelity: parse(pretty(p)) == p;
//   3. verifies that every import / re-export path resolves to an existing
//      `.hnl` file on disk (search roots: kit-stdlib/, examples/, file dir).
//
// This confirms that the multi-file import graphs resolve on disk, per
// ADR-0069 §7 ("Files Are Arrows" + multi-file programs).

#[path = "v0_1_surface.rs"]
mod v0_1_surface;

use v0_1_surface::{parse, pretty, Export, Import, Program};

use std::path::{Path, PathBuf};

/// Recursively collect every `.hnl` file under `dir` into `out`.
fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return, // missing directory: skip gracefully
    };
    for entry in entries.flatten() {
        let p = entry.path();
        if p.is_dir() {
            walk(&p, out);
        } else if p.extension().map_or(false, |e| e == "hnl") {
            out.push(p);
        }
    }
}

/// Collect all import and re-export paths referenced by a parsed program.
fn referenced_paths(p: &Program) -> Vec<String> {
    let mut v = Vec::new();
    for im in &p.imports {
        match im {
            Import::Names { path, .. } => v.push(path.clone()),
            Import::Whole { path, .. } => v.push(path.clone()),
        }
    }
    for ex in &p.exports {
        match ex {
            Export::NamesFrom { path, .. } => v.push(path.clone()),
            Export::AllFrom { path } => v.push(path.clone()),
            _ => {}
        }
    }
    v
}

/// Does `path` resolve to an existing `.hnl` file under any of the `roots`?
/// A `.hnl` extension is appended when the path has none (FileResolver rule).
fn resolves(roots: &[&Path], path: &str) -> bool {
    let mut p = PathBuf::from(path);
    if p.extension().is_none() {
        p.set_extension("hnl");
    }
    for root in roots {
        let mut full = root.to_path_buf();
        full.push(&p);
        if full.is_file() {
            return true;
        }
    }
    false
}

fn main() {
    let crate_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let kit_stdlib = crate_root.join("kit-stdlib");
    let examples = crate_root.join("examples");

    let mut files: Vec<PathBuf> = Vec::new();
    walk(&kit_stdlib, &mut files);
    walk(&examples, &mut files);
    files.sort();

    let mut failed = false;
    let mut count = 0usize;

    for f in &files {
        let rel = f
            .strip_prefix(&crate_root)
            .unwrap_or(f)
            .display()
            .to_string();
        count += 1;

        let src = match std::fs::read_to_string(f) {
            Ok(s) => s,
            Err(e) => {
                println!("FAIL read {}: {}", rel, e);
                failed = true;
                continue;
            }
        };

        // 1. Parse.
        let p: Program = match parse(&src) {
            Ok(p) => p,
            Err(e) => {
                println!("FAIL parse {}: {}", rel, e);
                failed = true;
                continue;
            }
        };
        println!("PASS parse {}", rel);

        // 2. Round-trip: parse(pretty(p)) == p.
        let pp = pretty(&p);
        match parse(&pp) {
            Ok(p2) => {
                if p2 == p {
                    println!("PASS round-trip {}", rel);
                } else {
                    println!("FAIL round-trip {}: re-parsed AST differs", rel);
                    failed = true;
                }
            }
            Err(e) => {
                println!("FAIL round-trip {}: re-parse error: {}", rel, e);
                failed = true;
            }
        }

        // 3. Import / re-export resolution on disk.
        let file_dir = f.parent().map(|x| x.to_path_buf()).unwrap_or_default();
        let roots: Vec<&Path> = vec![kit_stdlib.as_path(), examples.as_path(), file_dir.as_path()];
        let mut unresolved: Vec<String> = Vec::new();
        for ip in referenced_paths(&p) {
            if !resolves(&roots, &ip) {
                unresolved.push(ip);
            }
        }
        if unresolved.is_empty() {
            println!("PASS imports {}", rel);
        } else {
            println!("FAIL imports {}: unresolved: {}", rel, unresolved.join(", "));
            failed = true;
        }
    }

    if failed {
        println!("\nSome checks FAILED.");
        std::process::exit(1);
    }
    println!(
        "\nAll {} .hnl files parse, round-trip, and resolve.",
        count
    );
}
