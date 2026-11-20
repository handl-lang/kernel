use super::*;
use crate::fragments::CapabilityDecl;

#[test]
fn capability_is_union() {
    assert!(CapabilityDecl::UNION);
}
