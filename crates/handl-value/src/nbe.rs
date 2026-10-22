//! NbE semantic domain — `Val`/`Env`/metas for the shared evaluator and
//! the typecheck engine (phase-1 spec, `host/project/design/
//! phase1-typesystem-spec.md`; ADR-0106 as amended by 0152/0153/0154).
//!
//! The domain is *data*, not closures: `VArrow` is the self-contained
//! serializable arrow (`body_def` + `binds`), environments are an
//! explicit persistent list, neutrals are head+spine records. Nothing
//! in `Val` captures host-language state — every variant serializes or
//! is elaborator-internal (`Flex`/`Unfold` never cross a boundary).
//!
//! Conventions (smalltt/Kovács): de Bruijn *indices* in terms, de
//! Bruijn *levels* in values. `Lvl` counts binders from the outside;
//! a rigid head is a level, never a name.

use std::cell::OnceCell;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::rc::Rc;
use std::cell::RefCell;

use rustc_hash::FxHashMap;
use serde_json::Value;

use crate::{Sym, TaggedValue};

/// De Bruijn level — depth of a binder, counting outward.
pub type Lvl = u32;

/// Metavariable id — index into the [`MetaStore`].
pub type MetaId = u32;

/// The semantic domain. Every type the checker produces and every
/// value the evaluator normalizes lives here; `TaggedValue` is the
/// boundary encoding (serialization/FFI), `Val` is the semantics.
#[derive(Clone, Debug)]
pub enum Val {
    /// Rigid neutral: a free variable at `lvl` applied to `spine`
    /// eliminations. Cannot reduce further (the variable is bound in
    /// the context, not solved).
    Rigid { lvl: Lvl, spine: Spine },
    /// Flexible neutral: unsolved metavariable applied to a spine.
    /// Solved metas are substituted on read via the meta store.
    Flex { meta: MetaId, spine: Spine },
    /// A nominal former applied to indices — `Vec(2, Int)`,
    /// `Hom(2, f, g)`, `Type(i)`, `Arr(r, a, b)` (ADR-0152/0153).
    /// Head equality is `sym` identity; `args` are ordinary values.
    Former { head: Rc<Sym>, args: Vec<Val> },
    /// A nominal sym used as a value (a type object itself —
    /// `Int`, `Nat`). Equality is identity.
    Nominal(Rc<Sym>),
    /// Defunctionalized closure: the self-contained arrow value
    /// (`params` + `body_def` arena + explicit `binds` map). This is
    /// the same shape `TaggedValue::Arrow` carries — a "closure"
    /// spelled as inspectable, serializable data (ADR-0106 §3: no
    /// host-language closures, no hidden capture).
    Arrow(Rc<ArrowVal>),
    /// A universe level — `Type(i)` (ADR-0154 §4).
    Universe(u32),
    /// Boundary value: literals and plain data (numbers, strings,
    /// records) carried as `TaggedValue`. Anything the domain does not
    /// structure stays tagged — equality is structural (0154 §3).
    Const(TaggedValue),
    /// Controlled definition unfolding (Kovács): the top-level name
    /// plus its spine, with the unfolded value computed lazily.
    /// Conversion checks the name first (fast path) and forces only
    /// on failure — keeps meta solutions small and preserves
    /// unfoldings for printing.
    Unfold { name: Rc<str>, spine: Spine, value: Rc<OnceCell<Val>> },
}

/// The explicit closure payload of [`Val::Arrow`] — mirrors
/// `TaggedValue::Arrow`'s self-contained shape.
#[derive(Clone, Debug)]
pub struct ArrowVal {
    /// Parameter names.
    pub params: Rc<[String]>,
    /// The body as explicit data (`{"__ast__": …}` tagged value or
    /// a structured term — opaque here, interpreted by engines).
    pub body_def: TaggedValue,
    /// Residual explicit bindings (the environment, spelled as data).
    pub binds: Rc<FxHashMap<Rc<str>, Val>>,
}

/// Elimination spine — the arguments a neutral head is applied to.
/// Kept minimal: `App` covers arrow application and former
/// instantiation; projections ride along as data when needed.
#[derive(Clone, Debug, Default)]
pub struct Spine(pub Vec<Val>);

impl Spine {
    /// Append one application argument.
    pub fn push(&mut self, arg: Val) {
        self.0.push(arg);
    }

    /// Whether the spine is empty (a bare head).
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

/// A typing environment — persistent cons list, `Rc`-shared tails.
/// Extending is O(1) and never mutates a shared prefix; truncating is
/// dropping the head (the mark/restore discipline of the old Γ stack
/// becomes structural sharing).
#[derive(Clone, Debug, Default)]
pub struct Env(pub Option<Rc<EnvNode>>);

#[derive(Debug)]
pub struct EnvNode {
    /// The bound value (a rigid `Val::Rigid` for binders being
    /// checked; a real value for definitions).
    pub val: Val,
    /// Tail — outer bindings.
    pub next: Env,
    /// Optional declared name (for diagnostics; lookup is by level).
    pub name: Option<Rc<str>>,
}

impl Env {
    /// Empty environment.
    pub fn new() -> Self {
        Env(None)
    }

    /// Extend with a value — O(1), shares the tail.
    pub fn extend(&self, name: Option<Rc<str>>, val: Val) -> Env {
        Env(Some(Rc::new(EnvNode {
            val,
            next: self.clone(),
            name,
        })))
    }

    /// Look up by level offset (0 = innermost). Iterates the cons
    /// cells — O(depth of the binding), which is the NbE convention.
    pub fn lookup(&self, lvl_offset: u32) -> Option<&Val> {
        let mut cur = self;
        let mut i = lvl_offset;
        while let Some(node) = &cur.0 {
            if i == 0 {
                return Some(&node.val);
            }
            i -= 1;
            cur = &node.next;
        }
        None
    }

    /// Number of bindings (O(n)).
    pub fn len(&self) -> usize {
        let mut n = 0;
        let mut cur = self;
        while let Some(node) = &cur.0 {
            n += 1;
            cur = &node.next;
        }
        n
    }

    /// Whether the environment is empty.
    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }
}

/// A constraint attached to an unsolved metavariable — used by literal
/// typing (ADR-0154 §5): `DescendantOf(sym)` means the meta must solve
/// to a type whose `parent` chain contains `sym` (e.g. a numeric
/// literal solving only to a `type.number` descendant).
#[derive(Clone, Debug)]
pub enum MetaConstraint {
    /// Unconstrained — solves to any type.
    None,
    /// Must solve to a descendant (or the sym itself) of the given
    /// nominal.
    DescendantOf(Rc<Sym>),
}

/// One metavariable's state.
#[derive(Clone, Debug)]
pub struct MetaEntry {
    /// `Some(v)` once solved; `None` while open.
    pub solution: Option<Val>,
    /// Solving constraint — checked by `MetaStore::solve`.
    pub constraint: MetaConstraint,
}

/// The metavariable store — growable, owned by the checking context.
#[derive(Debug, Default)]
pub struct MetaStore {
    metas: Vec<MetaEntry>,
}

impl MetaStore {
    /// Allocate an unconstrained metavariable.
    pub fn fresh(&mut self) -> MetaId {
        self.metas.push(MetaEntry {
            solution: None,
            constraint: MetaConstraint::None,
        });
        (self.metas.len() - 1) as MetaId
    }

    /// Allocate a metavariable with a solving constraint.
    pub fn fresh_constrained(&mut self, c: MetaConstraint) -> MetaId {
        self.metas.push(MetaEntry {
            solution: None,
            constraint: c,
        });
        (self.metas.len() - 1) as MetaId
    }

    /// The solved value of a meta, if any.
    pub fn solution(&self, id: MetaId) -> Option<&Val> {
        self.metas
            .get(id as usize)
            .and_then(|e| e.solution.as_ref())
    }

    /// Solve a meta to `val`. Returns `false` (without solving) when
    /// `val` violates the meta's constraint; an occurs check against
    /// `id` inside `val` is the caller's responsibility (`occurs`).
    pub fn solve(&mut self, id: MetaId, val: Val) -> bool {
        let Some(entry) = self.metas.get_mut(id as usize) else {
            return false;
        };
        if entry.solution.is_some() {
            return false;
        }
        if let MetaConstraint::DescendantOf(sym) = &entry.constraint {
            // The solution's nominal head must have `sym` in its
            // parent chain — literal-type discipline (0154 §5).
            let ok = match &val {
                Val::Nominal(s) | Val::Former { head: s, .. } => {
                    s.has_ancestor(sym.as_ref())
                }
                _ => false,
            };
            if !ok {
                return false;
            }
        }
        entry.solution = Some(val);
        true
    }

    /// `occurs` — whether meta `id` appears anywhere inside `val`
    /// (through solved metas too). Called before `solve` to reject
    /// recursive solutions.
    pub fn occurs(&self, id: MetaId, val: &Val) -> bool {
        match val {
            Val::Flex { meta, spine } => {
                *meta == id || spine.0.iter().any(|v| self.occurs(id, v))
            }
            Val::Rigid { spine, .. } | Val::Unfold { spine, .. } => {
                spine.0.iter().any(|v| self.occurs(id, v))
            }
            Val::Former { args, .. } => args.iter().any(|v| self.occurs(id, v)),
            Val::Arrow(a) => a.binds.values().any(|v| self.occurs(id, v)),
            Val::Nominal(_) | Val::Universe(_) | Val::Const(_) => false,
        }
    }

    /// Read a value with all *solved* metas at the root substituted.
    /// Deep normalization walks the whole structure in the checker;
    /// this is just the head-forcing step conversion needs first.
    pub fn force_head<'v>(&'v self, val: &'v Val) -> &'v Val {
        let mut cur = val;
        while let Val::Flex { meta, spine } = cur {
            if !spine.is_empty() {
                // A solved meta under a spine needs full substitution —
                // the checker's `force` handles it; here we stop.
                break;
            }
            match self.solution(*meta) {
                Some(v) => cur = v,
                None => break,
            }
        }
        cur
    }
}

// ---------------------------------------------------------------------------
// Deterministic sym seeding (ADR-0154 §1)
// ---------------------------------------------------------------------------

// Registry of seeded syms — a declared former minted by qualified
// name resolves to one identity per process, and its *handle* is a
// content hash of the seed, so the same declaration yields the same
// nominal across module loads, compilation artifacts, and process
// boundaries (the ADR-0106 follow-up: cross-process `sym` identity).
thread_local! {
    static SEEDED_SYMS: RefCell<FxHashMap<String, Rc<Sym>>> =
        RefCell::new(FxHashMap::default());
}

// The high bit marks a seeded handle — fresh handles from
// `SYM_NEXT_HANDLE` stay low, so the two handle spaces never collide.
const SEEDED_BIT: u64 = 1 << 63;

impl Sym {
    /// Mint (or recall) the nominal for a declared name — e.g.
    /// `sym("vec.Vec")`. Idempotent within a process and *stable*
    /// across processes: the handle is a hash of `seed`, not the
    /// fresh counter, so serialized formers keep their identity.
    ///
    /// Use for `data` formers, exported type declarations, and any
    /// nominal that must be equal across module boundaries. Plain
    /// `Sym::fresh` remains correct for local/anonymous identities.
    pub fn seeded(seed: &str) -> Rc<Sym> {
        SEEDED_SYMS.with(|m| {
            let mut map = m.borrow_mut();
            if let Some(s) = map.get(seed) {
                return s.clone();
            }
            let mut h = DefaultHasher::new();
            seed.hash(&mut h);
            let handle = h.finish() | SEEDED_BIT;
            let name = seed
                .rsplit_once('.')
                .map(|(_, n)| n.to_string())
                .unwrap_or_else(|| seed.to_string());
            let sym = Rc::new(Sym::from_parts(handle, name, None, None));
            map.insert(seed.to_string(), sym.clone());
            sym
        })
    }

    /// Seeded nominal with an explicit parent — the deterministic
    /// counterpart of `fresh_with_parent`.
    ///
    /// If the seed was already minted *parentless* (a bare `seeded`
    /// call that ran before the declaration's parent was known), the
    /// memo entry is upgraded to a same-handle sym carrying the parent
    /// — identity is the handle, so existing values still compare
    /// equal. A sym that already has a parent is never re-parented.
    pub fn seeded_with_parent(seed: &str, parent: &Sym) -> Rc<Sym> {
        SEEDED_SYMS.with(|m| {
            let mut map = m.borrow_mut();
            if let Some(s) = map.get(seed) {
                if s.parent().is_some() {
                    return s.clone();
                }
                let upgraded = Rc::new(Sym::from_parts(
                    s.handle(),
                    s.name().to_string(),
                    Some(Rc::new(parent.clone())),
                    s.ty().cloned().map(Rc::new),
                ));
                map.insert(seed.to_string(), upgraded.clone());
                return upgraded;
            }
            let mut h = DefaultHasher::new();
            seed.hash(&mut h);
            let name = seed
                .rsplit_once('.')
                .map(|(_, n)| n.to_string())
                .unwrap_or_else(|| seed.to_string());
            let sym = Rc::new(Sym::from_parts(
                h.finish() | SEEDED_BIT,
                name,
                Some(Rc::new(parent.clone())),
                None,
            ));
            map.insert(seed.to_string(), sym.clone());
            sym
        })
    }

    /// Seeded nominal with both links — `parent` (the `<:` edge) and
    /// `ty` (the `type`/membership edge, ADR-0154 §2). This is the mint
    /// for declared *type* values: `Int := seeded_with_links(
    /// "type.Int", Number, Type)`.
    ///
    /// Upgrade semantics match `seeded_with_parent`: a memoized sym
    /// gains whichever links it is missing (same handle — mint order
    /// cannot orphan a link); a link already set is never rewritten.
    pub fn seeded_with_links(
        seed: &str,
        parent: Option<&Sym>,
        ty: Option<&Sym>,
    ) -> Rc<Sym> {
        SEEDED_SYMS.with(|m| {
            let mut map = m.borrow_mut();
            if let Some(s) = map.get(seed) {
                let needs_parent = s.parent().is_none() && parent.is_some();
                let needs_ty = s.ty().is_none() && ty.is_some();
                if !needs_parent && !needs_ty {
                    return s.clone();
                }
                let upgraded = Rc::new(Sym::from_parts(
                    s.handle(),
                    s.name().to_string(),
                    if needs_parent {
                        parent.map(|p| Rc::new(p.clone()))
                    } else {
                        s.parent().map(|p| Rc::new(p.clone()))
                    },
                    if needs_ty {
                        ty.map(|t| Rc::new(t.clone()))
                    } else {
                        s.ty().map(|t| Rc::new(t.clone()))
                    },
                ));
                map.insert(seed.to_string(), upgraded.clone());
                return upgraded;
            }
            let mut h = DefaultHasher::new();
            seed.hash(&mut h);
            let name = seed
                .rsplit_once('.')
                .map(|(_, n)| n.to_string())
                .unwrap_or_else(|| seed.to_string());
            let sym = Rc::new(Sym::from_parts(
                h.finish() | SEEDED_BIT,
                name,
                parent.map(|p| Rc::new(p.clone())),
                ty.map(|t| Rc::new(t.clone())),
            ));
            map.insert(seed.to_string(), sym.clone());
            sym
        })
    }

    /// The current memoized seeded sym with `handle`, if any — the
    /// upgraded (link-carrying) version of a sym minted before its
    /// links were declared. A captured `Sym` is immutable, so a stale
    /// `Int` minted bare keeps `parent = None` even after
    /// `seeded_with_links` upgrades the memo; readers that walk links
    /// re-resolve through here first (identity is the handle, so the
    /// substitution is semantics-preserving).
    pub fn seeded_by_handle(handle: u64) -> Option<Rc<Sym>> {
        if handle & SEEDED_BIT == 0 {
            return None;
        }
        SEEDED_SYMS.with(|m| {
            m.borrow()
                .values()
                .find(|s| s.handle() == handle)
                .cloned()
        })
    }

    /// This sym re-resolved through the seeded memo (see
    /// [`Sym::seeded_by_handle`]): fresh/unmemoized syms return
    /// unchanged.
    pub fn resealed(&self) -> Rc<Sym> {
        Sym::seeded_by_handle(self.handle()).unwrap_or_else(|| Rc::new(self.clone()))
    }

    /// Whether this is a seeded (declared) nominal — handle has the
    /// high bit set.
    pub fn is_seeded(&self) -> bool {
        self.handle() & SEEDED_BIT != 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn seeded_sym_is_stable_and_idempotent() {
        let a = Sym::seeded("vec.Vec");
        let b = Sym::seeded("vec.Vec");
        let c = Sym::seeded("list.List");
        assert!(Rc::ptr_eq(&a, &b));
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert!(a.is_seeded());
        assert_eq!(a.name(), "Vec");
        // Fresh syms never collide with seeded handles.
        let f = Sym::fresh("Vec");
        assert_ne!(*a, f);
        assert!(!f.is_seeded());
    }

    #[test]
    fn seeded_parent_chain() {
        let number = Sym::seeded("type.Number");
        let int = Sym::seeded_with_parent("type.Int", &number);
        assert!(int.is_descendant_of(&number));
        assert!(int.has_ancestor(&number));
        assert!(!number.is_descendant_of(&int));
    }

    #[test]
    fn seeded_parent_upgrades_parentless_mint() {
        // A bare `seeded` mint before the declaration is known does not
        // lock the nominal into parentlessness: `seeded_with_parent`
        // upgrades the memo entry (same handle — `==` still holds).
        let bare = Sym::seeded("type.decimal");
        let dec = Sym::seeded_with_parent("type.decimal", &Sym::seeded("type.number"));
        assert!(dec.is_descendant_of(&Sym::seeded("type.number")));
        assert_eq!(*bare, *dec);
        assert!(!Rc::ptr_eq(&bare, &dec));
        // A second parent declaration does not re-parent.
        let other = Sym::seeded_with_parent("type.decimal", &Sym::seeded("type.other"));
        assert!(Rc::ptr_eq(&dec, &other));
        assert!(!dec.is_descendant_of(&Sym::seeded("type.other")));
    }

    #[test]
    fn env_shares_tails() {
        let e = Env::new().extend(Some("a".into()), Val::Universe(0));
        let e2 = e.extend(Some("b".into()), Val::Rigid {
            lvl: 0,
            spine: Spine::default(),
        });
        assert_eq!(e2.len(), 2);
        assert!(matches!(e2.lookup(0), Some(Val::Rigid { .. })));
        assert!(matches!(e2.lookup(1), Some(Val::Universe(0))));
        // The outer env is unaffected (persistent).
        assert_eq!(e.len(), 1);
    }

    #[test]
    fn meta_constraint_descendant() {
        let mut store = MetaStore::default();
        let num = Sym::seeded("type.Number");
        let int = Sym::seeded_with_parent("type.Int", &num);
        let m = store.fresh_constrained(MetaConstraint::DescendantOf(num.clone()));
        // Solving to Int (a Number descendant) succeeds.
        assert!(store.solve(m, Val::Nominal(int.clone())));
        // A second solve is refused.
        assert!(!store.solve(m, Val::Nominal(num)));
    }

    #[test]
    fn meta_constraint_rejects_non_descendant() {
        let mut store = MetaStore::default();
        let num = Sym::seeded("type.Number");
        let s = Sym::seeded("type.Str");
        let m = store.fresh_constrained(MetaConstraint::DescendantOf(num));
        assert!(!store.solve(m, Val::Nominal(s)));
        assert!(store.solution(m).is_none());
    }

    #[test]
    fn occurs_finds_flex_meta() {
        let store = MetaStore::default();
        let nested = Val::Flex {
            meta: 7,
            spine: Spine(vec![Val::Universe(0)]),
        };
        let outer = Val::Former {
            head: Sym::seeded("type.Vec"),
            args: vec![nested],
        };
        assert!(store.occurs(7, &outer));
        assert!(!store.occurs(9, &outer));
    }
}

// ---------------------------------------------------------------------------
// Conversion — `conv` (0154 §2/§3: nominal identity for heads, structural
// for bodies; metas solve, rigid levels compare)
// ---------------------------------------------------------------------------

/// Conversion check `a ≡ b` at ambient level `lvl` (the number of
/// binders in scope — needed to compare open terms). Solves unsolved
/// metas as a side effect; a failed `conv` may leave the store
/// partially solved — callers snapshot `MetaStore::mark`/`truncate`.
pub fn conv(store: &mut MetaStore, lvl: Lvl, a: &Val, b: &Val) -> bool {
    let a = store.force_head(a).clone();
    let b = store.force_head(b).clone();
    match (a, b) {
        // A solved-or-unsolved meta on the left: try to solve it to b
        // (occurs check first — ?m ≠ spine containing ?m).
        (Val::Flex { meta, .. }, other) | (other, Val::Flex { meta, .. }) => {
            !store.occurs(meta, &other) && store.solve(meta, other)
        }
        (Val::Rigid { lvl: l1, spine: s1 }, Val::Rigid { lvl: l2, spine: s2 }) => {
            l1 == l2 && conv_spine(store, lvl, &s1, &s2)
        }
        // Nominal heads compare by sym identity; index arguments by
        // structural conversion (0152 §1 / 0154 §3).
        (
            Val::Former { head: h1, args: a1 },
            Val::Former { head: h2, args: a2 },
        ) => {
            h1 == h2
                && a1.len() == a2.len()
                && a1.iter().zip(a2.iter()).all(|(x, y)| conv(store, lvl, x, y))
        }
        (Val::Nominal(s1), Val::Nominal(s2)) => s1 == s2,
        (Val::Universe(i), Val::Universe(j)) => i == j,
        (Val::Const(v1), Val::Const(v2)) => v1 == v2,
        // Arrows are data: params + residual binds compare structurally;
        // body_def compares by its tagged encoding (alpha-equivalence of
        // bodies is an engine concern — two identical definitions are
        // equal here, which is what transport/match need).
        (Val::Arrow(x), Val::Arrow(y)) => {
            x.params == y.params
                && x.body_def == y.body_def
                && x.binds.len() == y.binds.len()
                && x.binds.iter().all(|(k, v)| {
                    y.binds.get(k).is_some_and(|w| conv(store, lvl, v, w))
                })
        }
        // Unfold: same top-level name is the fast path (Kovács); on a
        // name mismatch force both sides and retry — a failed name
        // compare must not poison the store.
        (Val::Unfold { name: n1, .. }, Val::Unfold { name: n2, .. }) if n1 == n2 => true,
        (u @ Val::Unfold { .. }, other) | (other, u @ Val::Unfold { .. }) => {
            if let Val::Unfold { value, .. } = u {
                if let Some(v) = value.get() {
                    return conv(store, lvl, v, &other);
                }
            }
            false
        }
        _ => false,
    }
}

fn conv_spine(store: &mut MetaStore, lvl: Lvl, s1: &Spine, s2: &Spine) -> bool {
    s1.0.len() == s2.0.len()
        && s1.0.iter().zip(s2.0.iter()).all(|(x, y)| conv(store, lvl, x, y))
}

impl MetaStore {
    /// Snapshot mark — for backtracking a failed `conv`/`unify`.
    pub fn mark(&self) -> usize {
        self.metas.len()
    }

    /// Restore the store to `mark` — drops all metas allocated since
    /// (solutions to older metas are unaffected, which is the NbE
    /// convention: meta solving is monotone).
    pub fn truncate(&mut self, mark: usize) {
        self.metas.truncate(mark);
    }
}

#[cfg(test)]
mod conv_tests {
    use super::*;

    #[test]
    fn former_conv_nominal_head_structural_args() {
        let mut store = MetaStore::default();
        let vec = Sym::seeded("vec.Vec");
        let int = Sym::seeded("type.Int");
        let two_a = Val::Former {
            head: vec.clone(),
            args: vec![Val::Const(TaggedValue::Int(2)), Val::Nominal(int.clone())],
        };
        let two_b = Val::Former {
            head: vec.clone(),
            args: vec![Val::Const(TaggedValue::Int(2)), Val::Nominal(int)],
        };
        assert!(conv(&mut store, 0, &two_a, &two_b));
        let three = Val::Former {
            head: vec,
            args: vec![Val::Const(TaggedValue::Int(3)), Val::Nominal(Sym::seeded("type.Int"))],
        };
        assert!(!conv(&mut store, 0, &two_a, &three));
    }

    #[test]
    fn flex_solves_to_rigid() {
        let mut store = MetaStore::default();
        let m = store.fresh();
        let r = Val::Rigid { lvl: 0, spine: Spine::default() };
        assert!(conv(&mut store, 1, &Val::Flex { meta: m, spine: Spine::default() }, &r));
        assert!(store.solution(m).is_some());
    }

    #[test]
    fn flex_occurs_rejects_cycle() {
        let mut store = MetaStore::default();
        let m = store.fresh();
        let cyclic = Val::Former {
            head: Sym::seeded("type.Int"),
            args: vec![Val::Flex { meta: m, spine: Spine::default() }],
        };
        assert!(!conv(&mut store, 0, &Val::Flex { meta: m, spine: Spine::default() }, &cyclic));
        assert!(store.solution(m).is_none());
    }

    #[test]
    fn literal_meta_solves_numeric() {
        let mut store = MetaStore::default();
        let num = Sym::seeded("type.Number");
        let int = Sym::seeded_with_parent("type.Int", &num);
        let m = store.fresh_constrained(MetaConstraint::DescendantOf(num));
        assert!(conv(&mut store, 0, &Val::Flex { meta: m, spine: Spine::default() }, &Val::Nominal(int)));
        // A non-numeric type cannot solve the literal meta.
        let m2 = store.fresh_constrained(MetaConstraint::DescendantOf(Sym::seeded("type.Number")));
        assert!(!conv(&mut store, 0, &Val::Flex { meta: m2, spine: Spine::default() },
                     &Val::Nominal(Sym::seeded("type.Str"))));
    }
}

// ---------------------------------------------------------------------------
// Quote — reify a `Val` back to `TaggedValue` boundary data.
//
// `quote` maps the semantic domain onto the same tagged encoding the
// engines already serialize (`{"__neutral__"}` for open terms,
// `{"__former__"}`/`{"__sym__"}` for formers/nominals, `{"__meta__"}`
// for unsolved metas). `Term`/AST-shaped reification lives in the
// checker — `handl-value` stays dependency-free (it cannot see
// `handl-language`).
// ---------------------------------------------------------------------------

/// Reify `val` at ambient level `lvl` (needed to print rigid levels as
/// indices — smalltt convention: quote converts level → index).
/// `names`, when provided, supplies display names for binders in
/// outermost-first order (diagnostics only; identity is the level).
pub fn quote(store: &MetaStore, lvl: Lvl, val: &Val) -> TaggedValue {
    fn qv(store: &MetaStore, lvl: Lvl, val: &Val) -> Value {
        let q = |v: &Val| qv(store, lvl, v);
        match store.force_head(val) {
            Val::Rigid { lvl: l, spine } => serde_json::json!({
                "__neutral__": {
                    "head": "rigid",
                    "index": lvl.saturating_sub(l + 1),
                    "spine": spine.0.iter().map(q).collect::<Vec<_>>(),
                }
            }),
            Val::Flex { meta, spine } => serde_json::json!({
                "__neutral__": {
                    "head": "meta",
                    "id": meta,
                    "spine": spine.0.iter().map(q).collect::<Vec<_>>(),
                }
            }),
            Val::Former { head, args } => serde_json::json!({
                "__former__": {
                    "sym": Value::from(TaggedValue::Sym(head.clone())),
                    "args": args.iter().map(q).collect::<Vec<_>>(),
                }
            }),
            Val::Nominal(s) => Value::from(TaggedValue::Sym(s.clone())),
            Val::Universe(i) => serde_json::json!({"__type__": i}),
            Val::Const(v) => Value::from(v.clone()),
            Val::Arrow(a) => {
                let binds: serde_json::Map<String, Value> = a
                    .binds
                    .iter()
                    .map(|(k, v)| (k.to_string(), q(v)))
                    .collect();
                serde_json::json!({
                    "__arrow__": {
                        "params": a.params.iter().collect::<Vec<_>>(),
                        "binds": binds,
                    }
                })
            }
            Val::Unfold { name, spine, .. } => serde_json::json!({
                "__neutral__": {
                    "head": "unfold",
                    "name": name.as_ref(),
                    "spine": spine.0.iter().map(q).collect::<Vec<_>>(),
                }
            }),
        }
    }
    TaggedValue::from(qv(store, lvl, val))
}

#[cfg(test)]
mod quote_tests {
    use super::*;

    #[test]
    fn quote_former_and_neutral() {
        let store = MetaStore::default();
        let v = Val::Former {
            head: Sym::seeded("vec.Vec"),
            args: vec![
                Val::Rigid { lvl: 0, spine: Spine::default() },
                Val::Nominal(Sym::seeded("type.Int")),
            ],
        };
        let q = quote(&store, 1, &v);
        let j = Value::from(q);
        assert_eq!(j["__former__"]["sym"]["__sym__"]["name"], "Vec");
        assert_eq!(j["__former__"]["args"][0]["__neutral__"]["index"], 0);
    }

    #[test]
    fn quote_solved_meta_shows_solution() {
        let mut store = MetaStore::default();
        let m = store.fresh();
        store.solve(m, Val::Universe(0));
        let v = Val::Flex { meta: m, spine: Spine::default() };
        let j = Value::from(quote(&store, 0, &v));
        assert_eq!(j["__type__"], 0);
    }
}
