use super::*;

#[test]
fn v2_constructs() {
    let v = SchemeVersion::v2();
    assert_eq!(v.as_str(), "v2");
    assert_eq!(v.to_string(), "v2");
}

#[test]
fn default_is_v2() {
    assert_eq!(SchemeVersion::default(), SchemeVersion::v2());
}

#[test]
fn supports_accepts_same_version() {
    let engine = SchemeVersion::v2();
    let lang = SchemeVersion::v2();
    assert!(engine.supports(&lang));
}

#[test]
fn supports_rejects_unrelated_version() {
    let engine = SchemeVersion::v2();
    let lang = SchemeVersion::new("v3");
    assert!(!engine.supports(&lang));
}

#[test]
fn serde_roundtrip() {
    let v = SchemeVersion::v2();
    let j = serde_json::to_string(&v).unwrap();
    assert_eq!(j, "\"v2\"");
    let back: SchemeVersion = serde_json::from_str(&j).unwrap();
    assert_eq!(v, back);
}

#[test]
fn equality() {
    assert_eq!(SchemeVersion::v2(), SchemeVersion::new("v2"));
    assert_ne!(SchemeVersion::v2(), SchemeVersion::new("v3"));
}
