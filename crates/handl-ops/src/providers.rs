//! Atom-provider discovery for kernel-ABI (`handl_ops::Op`) impls.
//!
//! P-013 phase 2a (proposal-0012): a kernel-side provider crate submits
//! one [`KernelAtomProvider`] per crate via [`inventory::submit!`]; the
//! host's `handl-plugin-lib-handl` aggregates these with host-side
//! `AtomProvider` submissions into a single discovery view.
//!
//! The inventory only sees submissions from crates that are *linked* —
//! referencing a provider's public symbol is what pulls its `submit!`
//! object into the final artifact. Providers therefore also expose a
//! link anchor (`pub fn` in the same file as `submit!`); the host or
//! kit composition root calls it once.
//!
//! [`inventory::submit!`]: https://docs.rs/inventory

use std::sync::Arc;

use crate::Op;

/// One kernel-ABI atom impl: `(qualified op name, op)`.
pub type KernelAtomImpl = (&'static str, Arc<dyn Op>);

/// Impl-table constructor — same shape as host-side `ImplTable`.
pub type KernelImplTable = fn() -> Vec<KernelAtomImpl>;

/// A kernel-side atom provider: declares which module names its
/// `atoms.yaml` + impl table serve.
///
/// Submit exactly once per crate:
///
/// ```ignore
/// inventory::submit! {
///     handl_ops::KernelAtomProvider {
///         modules: &["my-mod"],
///         atoms_yaml: MY_ATOMS_YAML,   // `include_str!("atoms.yaml")`
///         impls: my_kernel_impls,      // fn() -> Vec<KernelAtomImpl>
///     }
/// }
/// ```
pub struct KernelAtomProvider {
    /// Module names this provider's `atoms.yaml` declares.
    pub modules: &'static [&'static str],
    /// The `atoms.yaml` text (`include_str!` of the dep's spec file).
    pub atoms_yaml: &'static str,
    /// Constructor for the `(op name, impl)` table.
    pub impls: KernelImplTable,
}

inventory::collect!(KernelAtomProvider);

/// All kernel-ABI atom providers linked into this binary, in
/// submission (link) order.
pub fn kernel_atom_providers() -> impl Iterator<Item = &'static KernelAtomProvider> {
    inventory::iter::<KernelAtomProvider>().into_iter()
}
