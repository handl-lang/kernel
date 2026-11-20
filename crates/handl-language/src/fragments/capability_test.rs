use super::*;

#[test]
fn construct_and_accessors() {
    let c = CapabilityDecl::new("fs.read")
        .with_description("read files")
        .with_replaces(vec!["fs.read.old".into()])
        .with_requires(vec!["fs.open".into()]);
    assert_eq!(c.id(), "fs.read");
    assert_eq!(c.description.as_deref(), Some("read files"));
    assert_eq!(c.replaces(), &["fs.read.old".to_string()]);
    assert_eq!(c.requires(), &["fs.open".to_string()]);
    assert_eq!(c.identity_key(), "fs.read");
    assert!(CapabilityDecl::UNION);
}

#[test]
fn serde_roundtrip() {
    let c = CapabilityDecl::new("net.connect").with_description("network");
    let j = serde_json::to_string(&c).unwrap();
    let back: CapabilityDecl = serde_json::from_str(&j).unwrap();
    assert_eq!(c, back);
}

#[test]
fn equality() {
    assert_eq!(CapabilityDecl::new("a"), CapabilityDecl::new("a"));
    assert_ne!(CapabilityDecl::new("a"), CapabilityDecl::new("b"));
}
