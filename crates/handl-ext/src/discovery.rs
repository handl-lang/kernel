//! Discovery: where extensions come from (ADR-0149 §5).
//!
//! Search order:
//!
//! 1. `--ext-dir <dir>` flags (repeatable) — highest precedence;
//! 2. `$HANDL_EXT_DIR` (a `PATH`-style list) — when no flag dirs;
//! 3. `~/.handl/ext/` — when neither flags nor the env var are set;
//! 4. dev builds (`debug_assertions`): `<exe-dir>/ext/` and `<exe-dir>`
//!    itself (which is the workspace `target/debug/` for a `cargo build`
//!    artifact), so a freshly `cargo build`ed `libhnl_ext_*` is picked up
//!    with no configuration.
//!
//! All applicable dirs are *unioned*: a `fmt` extension in `~/.handl/ext`
//! and a `lint` extension in `--ext-dir` both load. On conflicts the
//! earlier-precedence dir wins and the loser is recorded for `ext doctor`.

use std::collections::BTreeMap;
use std::path::PathBuf;

use crate::load::{DirScan, LoadFailure, LoadedExtension, load_dir};

/// Where a candidate directory came from (drives `ext doctor` output).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DirSource {
    /// `--ext-dir` on the command line.
    Flag,
    /// `$HANDL_EXT_DIR`.
    Env,
    /// `~/.handl/ext/`.
    Home,
    /// `<exe-dir>/ext/` — dev builds only.
    ExeDirExt,
    /// `<exe-dir>` itself — dev builds only (`target/debug` contains the
    /// freshly built `libhnl_ext_*` artifacts).
    ExeDir,
}

impl DirSource {
    /// Human label for `ext doctor`.
    pub fn label(self) -> &'static str {
        match self {
            DirSource::Flag => "--ext-dir",
            DirSource::Env => "$HANDL_EXT_DIR",
            DirSource::Home => "~/.handl/ext",
            DirSource::ExeDirExt => "<exe>/ext (dev)",
            DirSource::ExeDir => "<exe> (dev)",
        }
    }
}

/// A directory that was (or would be) searched, annotated for diagnostics.
#[derive(Debug, Clone)]
pub struct CandidateDir {
    /// The directory path.
    pub path: PathBuf,
    /// Which rule produced it.
    pub source: DirSource,
    /// Whether it existed at discovery time.
    pub exists: bool,
}

/// The default user extension directory: `~/.handl/ext`.
pub fn home_ext_dir() -> Option<PathBuf> {
    std::env::home_dir().map(|h| h.join(".handl").join("ext"))
}

/// The candidate directories for `flag_dirs`, in precedence order.
///
/// `flag_dirs` are the host's `--ext-dir` values; when non-empty they
/// replace the env/home fallbacks (per the ADR's `→` chain). The dev-scan
/// dirs are always appended under `debug_assertions`.
pub fn candidate_dirs(flag_dirs: &[PathBuf]) -> Vec<CandidateDir> {
    let mut out: Vec<(PathBuf, DirSource)> = Vec::new();

    if !flag_dirs.is_empty() {
        out.extend(flag_dirs.iter().cloned().map(|d| (d, DirSource::Flag)));
    } else if let Ok(env) = std::env::var("HANDL_EXT_DIR") {
        out.extend(
            std::env::split_paths(&env)
                .map(|d| (d, DirSource::Env))
                .collect::<Vec<_>>(),
        );
    } else if let Some(home) = home_ext_dir() {
        out.push((home, DirSource::Home));
    }

    // Dev builds additionally scan next to the executable so
    // `cargo build && hnl <cmd>` picks up `target/debug/libhnl_ext_*`
    // artifacts with zero setup.
    if cfg!(debug_assertions) {
        if let Ok(exe) = std::env::current_exe() {
            if let Some(dir) = exe.parent() {
                out.push((dir.join("ext"), DirSource::ExeDirExt));
                out.push((dir.to_path_buf(), DirSource::ExeDir));
            }
        }
    }

    out.into_iter()
        .map(|(path, source)| CandidateDir {
            exists: path.is_dir(),
            path,
            source,
        })
        .collect()
}

/// The outcome of a full discovery pass.
#[derive(Debug, Default)]
pub struct Discovery {
    /// Every directory considered, with its provenance and existence.
    pub dirs: Vec<CandidateDir>,
    /// Extensions that loaded, in directory-precedence order.
    pub extensions: Vec<LoadedExtension>,
    /// Candidate files that matched the naming convention but failed.
    pub failures: Vec<LoadFailure>,
    /// `(extension name, losing path)` pairs dropped because an extension
    /// with the same name was already loaded from an earlier dir.
    pub skipped_duplicates: Vec<(String, PathBuf)>,
}

impl Discovery {
    /// Find the extension serving `command`, in precedence order.
    pub fn find_command(&self, command: &str) -> Option<&LoadedExtension> {
        self.extensions
            .iter()
            .find(|e| e.command_names().any(|c| c == command))
    }

    /// `command name → [extension names]`, sorted by command — the table
    /// `hnl --help` renders.
    pub fn command_table(&self) -> BTreeMap<&str, Vec<&str>> {
        let mut table: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        for ext in &self.extensions {
            for spec in &ext.manifest().commands {
                table
                    .entry(spec.name.as_str())
                    .or_default()
                    .push(ext.manifest().name.as_str());
            }
        }
        table
    }
}

/// Run discovery: enumerate [`candidate_dirs`], scan each, and dedup
/// extensions by manifest name (earlier dir wins).
///
/// The same file reached through two dirs (symlinked or literal duplicates
/// — e.g. `--ext-dir target/debug` plus the dev `<exe>` scan) is loaded once.
pub fn discover(flag_dirs: &[PathBuf]) -> Discovery {
    let mut discovery = Discovery::default();
    discovery.dirs = candidate_dirs(flag_dirs);

    let mut seen_files: Vec<PathBuf> = Vec::new();
    let mut seen_names: Vec<String> = Vec::new();

    for dir in &discovery.dirs {
        if !dir.exists {
            continue;
        }
        let DirScan { loaded, failures } = load_dir(&dir.path);
        discovery.failures.extend(failures);
        for ext in loaded {
            // Same file via two dirs → keep the first.
            let key = std::fs::canonicalize(ext.path()).unwrap_or_else(|_| ext.path().to_path_buf());
            if seen_files.contains(&key) {
                continue;
            }
            seen_files.push(key);
            // Same extension name via two files → earlier dir wins.
            let name = ext.manifest().name.clone();
            if seen_names.contains(&name) {
                discovery
                    .skipped_duplicates
                    .push((name, ext.path().to_path_buf()));
                continue;
            }
            seen_names.push(name);
            discovery.extensions.push(ext);
        }
    }
    discovery
}
