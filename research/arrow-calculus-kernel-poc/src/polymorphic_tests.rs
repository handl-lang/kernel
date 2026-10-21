// Challenge #3: Parametricity via Polymorphic Arrow Types
// Tests for type variables and generic arrow patterns
//
// Key questions:
// 1. Can we express polymorphic arrow types (forall a. a ~> a)?
// 2. Can arrows be instantiated with different types?
// 3. Do generic combinators work across types?

use std::fmt;

// ============================================================================
// Polymorphic Value Type System
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
pub enum PolyType {
    // Ground types
    Int,
    Bool,
    Unit,
    String,
    
    // Type variables (for polymorphism)
    Var(String),
    
    // Compound types
    Arrow(Box<PolyType>, Box<PolyType>),
    List(Box<PolyType>),
    Product(Box<PolyType>, Box<PolyType>),
    Sum(Box<PolyType>, Box<PolyType>),
    
    // Quantified types (forall a. type)
    Forall(String, Box<PolyType>),
}

impl fmt::Display for PolyType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PolyType::Int => write!(f, "Int"),
            PolyType::Bool => write!(f, "Bool"),
            PolyType::Unit => write!(f, "()"),
            PolyType::String => write!(f, "String"),
            PolyType::Var(name) => write!(f, "{}", name),
            PolyType::Arrow(a, b) => write!(f, "{} ~> {}", a, b),
            PolyType::List(t) => write!(f, "[{}]", t),
            PolyType::Product(a, b) => write!(f, "({}, {})", a, b),
            PolyType::Sum(a, b) => write!(f, "{} | {}", a, b),
            PolyType::Forall(var, ty) => write!(f, "forall {}. {}", var, ty),
        }
    }
}

// ============================================================================
// Type Substitution: Instantiate type variables
// ============================================================================

pub struct TypeSubst {
    bindings: std::collections::HashMap<String, PolyType>,
}

impl TypeSubst {
    pub fn new() -> Self {
        TypeSubst {
            bindings: std::collections::HashMap::new(),
        }
    }

    pub fn bind(mut self, var: String, ty: PolyType) -> Self {
        self.bindings.insert(var, ty);
        self
    }

    pub fn apply(&self, ty: &PolyType) -> PolyType {
        match ty {
            PolyType::Var(name) => {
                self.bindings.get(name).cloned().unwrap_or_else(|| PolyType::Var(name.clone()))
            }
            PolyType::Arrow(a, b) => {
                PolyType::Arrow(
                    Box::new(self.apply(a)),
                    Box::new(self.apply(b)),
                )
            }
            PolyType::List(t) => PolyType::List(Box::new(self.apply(t))),
            PolyType::Product(a, b) => {
                PolyType::Product(
                    Box::new(self.apply(a)),
                    Box::new(self.apply(b)),
                )
            }
            PolyType::Sum(a, b) => {
                PolyType::Sum(
                    Box::new(self.apply(a)),
                    Box::new(self.apply(b)),
                )
            }
            PolyType::Forall(var, body) => {
                // Don't substitute inside quantifiers for now (simple implementation)
                PolyType::Forall(var.clone(), Box::new(self.apply(body)))
            }
            other => other.clone(),
        }
    }
}

// ============================================================================
// Polymorphic Arrow Patterns
// ============================================================================

// Experiment 1: Identity arrow (most polymorphic)
// Type: forall a. a ~> a
pub fn poly_identity_type() -> PolyType {
    PolyType::Forall(
        "a".to_string(),
        Box::new(PolyType::Arrow(
            Box::new(PolyType::Var("a".to_string())),
            Box::new(PolyType::Var("a".to_string())),
        )),
    )
}

// Instantiate identity at Int
pub fn poly_identity_at_int() -> PolyType {
    let ty = poly_identity_type();
    match &ty {
        PolyType::Forall(var, body) => {
            let subst = TypeSubst::new().bind(var.clone(), PolyType::Int);
            subst.apply(&body)
        }
        _ => ty,
    }
}

// Instantiate identity at [Int]
pub fn poly_identity_at_list_int() -> PolyType {
    let ty = poly_identity_type();
    match &ty {
        PolyType::Forall(var, body) => {
            let subst = TypeSubst::new().bind(var.clone(), PolyType::List(Box::new(PolyType::Int)));
            subst.apply(&body)
        }
        _ => ty,
    }
}

// ============================================================================
// Experiment 2: Const arrow (selects first of two)
// Type: forall a b. a ~> (b ~> a)
// ============================================================================

pub fn poly_const_type() -> PolyType {
    PolyType::Forall(
        "a".to_string(),
        Box::new(PolyType::Forall(
            "b".to_string(),
            Box::new(PolyType::Arrow(
                Box::new(PolyType::Var("a".to_string())),
                Box::new(PolyType::Arrow(
                    Box::new(PolyType::Var("b".to_string())),
                    Box::new(PolyType::Var("a".to_string())),
                )),
            )),
        )),
    )
}

// Instantiate const at Int, Bool
pub fn poly_const_at_int_bool() -> PolyType {
    let ty = poly_const_type();
    match &ty {
        PolyType::Forall(var_a, body_a) => {
            match &**body_a {
                PolyType::Forall(var_b, body_ab) => {
                    let subst = TypeSubst::new()
                        .bind(var_a.clone(), PolyType::Int)
                        .bind(var_b.clone(), PolyType::Bool);
                    subst.apply(&body_ab)
                }
                _ => ty,
            }
        }
        _ => ty,
    }
}

// ============================================================================
// Experiment 3: Compose arrow (composition)
// Type: forall a b c. (a ~> b) ~> (b ~> c) ~> (a ~> c)
// ============================================================================

pub fn poly_compose_type() -> PolyType {
    PolyType::Forall(
        "a".to_string(),
        Box::new(PolyType::Forall(
            "b".to_string(),
            Box::new(PolyType::Forall(
                "c".to_string(),
                Box::new(PolyType::Arrow(
                    Box::new(PolyType::Arrow(
                        Box::new(PolyType::Var("a".to_string())),
                        Box::new(PolyType::Var("b".to_string())),
                    )),
                    Box::new(PolyType::Arrow(
                        Box::new(PolyType::Arrow(
                            Box::new(PolyType::Var("b".to_string())),
                            Box::new(PolyType::Var("c".to_string())),
                        )),
                        Box::new(PolyType::Arrow(
                            Box::new(PolyType::Var("a".to_string())),
                            Box::new(PolyType::Var("c".to_string())),
                        )),
                    )),
                )),
            )),
        )),
    )
}

// Instantiate compose at Int -> String -> Bool
pub fn poly_compose_at_int_string_bool() -> PolyType {
    let ty = poly_compose_type();
    match &ty {
        PolyType::Forall(var_a, body_a) => {
            match &**body_a {
                PolyType::Forall(var_b, body_ab) => {
                    match &**body_ab {
                        PolyType::Forall(var_c, body_abc) => {
                            let subst = TypeSubst::new()
                                .bind(var_a.clone(), PolyType::Int)
                                .bind(var_b.clone(), PolyType::String)
                                .bind(var_c.clone(), PolyType::Bool);
                            subst.apply(&body_abc)
                        }
                        _ => ty,
                    }
                }
                _ => ty,
            }
        }
        _ => ty,
    }
}

// ============================================================================
// Experiment 4: Map arrow (list transformation)
// Type: forall a b. (a ~> b) ~> ([a] ~> [b])
// ============================================================================

pub fn poly_map_type() -> PolyType {
    PolyType::Forall(
        "a".to_string(),
        Box::new(PolyType::Forall(
            "b".to_string(),
            Box::new(PolyType::Arrow(
                Box::new(PolyType::Arrow(
                    Box::new(PolyType::Var("a".to_string())),
                    Box::new(PolyType::Var("b".to_string())),
                )),
                Box::new(PolyType::Arrow(
                    Box::new(PolyType::List(Box::new(PolyType::Var("a".to_string())))),
                    Box::new(PolyType::List(Box::new(PolyType::Var("b".to_string())))),
                )),
            )),
        )),
    )
}

// Instantiate map at Int -> Bool
pub fn poly_map_at_int_bool() -> PolyType {
    let ty = poly_map_type();
    match &ty {
        PolyType::Forall(var_a, body_a) => {
            match &**body_a {
                PolyType::Forall(var_b, body_ab) => {
                    let subst = TypeSubst::new()
                        .bind(var_a.clone(), PolyType::Int)
                        .bind(var_b.clone(), PolyType::Bool);
                    subst.apply(&body_ab)
                }
                _ => ty,
            }
        }
        _ => ty,
    }
}

// ============================================================================
// Experiment 5: Generic Fold
// Type: forall a b. (b ~> (a ~> b)) ~> (b ~> ([a] ~> b))
// ============================================================================

pub fn poly_fold_type() -> PolyType {
    PolyType::Forall(
        "a".to_string(),
        Box::new(PolyType::Forall(
            "b".to_string(),
            Box::new(PolyType::Arrow(
                Box::new(PolyType::Arrow(
                    Box::new(PolyType::Var("b".to_string())),
                    Box::new(PolyType::Arrow(
                        Box::new(PolyType::Var("a".to_string())),
                        Box::new(PolyType::Var("b".to_string())),
                    )),
                )),
                Box::new(PolyType::Arrow(
                    Box::new(PolyType::Var("b".to_string())),
                    Box::new(PolyType::Arrow(
                        Box::new(PolyType::List(Box::new(PolyType::Var("a".to_string())))),
                        Box::new(PolyType::Var("b".to_string())),
                    )),
                )),
            )),
        )),
    )
}

// Instantiate fold at Int elements, Bool accumulator
pub fn poly_fold_at_int_bool() -> PolyType {
    let ty = poly_fold_type();
    match &ty {
        PolyType::Forall(var_a, body_a) => {
            match &**body_a {
                PolyType::Forall(var_b, body_ab) => {
                    let subst = TypeSubst::new()
                        .bind(var_a.clone(), PolyType::Int)
                        .bind(var_b.clone(), PolyType::Bool);
                    subst.apply(&body_ab)
                }
                _ => ty,
            }
        }
        _ => ty,
    }
}

// ============================================================================
// Test Suite
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_poly_identity_type() {
        let ty = poly_identity_type();
        assert!(format!("{}", ty).contains("forall"));
        assert!(format!("{}", ty).contains("~>"));
    }

    #[test]
    fn test_poly_identity_instantiate_int() {
        let ty = poly_identity_at_int();
        let ty_str = format!("{}", ty);
        assert_eq!(ty_str, "Int ~> Int", "Identity at Int should be Int -> Int");
    }

    #[test]
    fn test_poly_identity_instantiate_list_int() {
        let ty = poly_identity_at_list_int();
        let ty_str = format!("{}", ty);
        assert_eq!(ty_str, "[Int] ~> [Int]", "Identity at [Int] should be [Int] -> [Int]");
    }

    #[test]
    fn test_poly_const_type() {
        let ty = poly_const_type();
        assert!(format!("{}", ty).contains("forall"));
    }

    #[test]
    fn test_poly_const_instantiate() {
        let ty = poly_const_at_int_bool();
        let ty_str = format!("{}", ty);
        // Should have Int and Bool somewhere
        assert!(ty_str.contains("Int"));
        assert!(ty_str.contains("Bool"));
    }

    #[test]
    fn test_poly_compose_type() {
        let ty = poly_compose_type();
        assert!(format!("{}", ty).contains("forall"));
    }

    #[test]
    fn test_poly_compose_instantiate() {
        let ty = poly_compose_at_int_string_bool();
        let ty_str = format!("{}", ty);
        // Should have all three types
        assert!(ty_str.contains("Int"));
        assert!(ty_str.contains("String"));
        assert!(ty_str.contains("Bool"));
    }

    #[test]
    fn test_poly_map_type() {
        let ty = poly_map_type();
        assert!(format!("{}", ty).contains("forall"));
        assert!(format!("{}", ty).contains("["));
    }

    #[test]
    fn test_poly_map_instantiate_int_bool() {
        let ty = poly_map_at_int_bool();
        let ty_str = format!("{}", ty);
        assert!(ty_str.contains("[Int]"));
        assert!(ty_str.contains("[Bool]"));
    }

    #[test]
    fn test_poly_fold_type() {
        let ty = poly_fold_type();
        assert!(format!("{}", ty).contains("forall"));
    }

    #[test]
    fn test_poly_fold_instantiate() {
        let ty = poly_fold_at_int_bool();
        let ty_str = format!("{}", ty);
        assert!(ty_str.contains("Int"));
        assert!(ty_str.contains("Bool"));
    }

    #[test]
    fn test_type_substitution_basic() {
        let ty = PolyType::Var("a".to_string());
        let subst = TypeSubst::new().bind("a".to_string(), PolyType::Int);
        let result = subst.apply(&ty);
        assert_eq!(result, PolyType::Int);
    }

    #[test]
    fn test_type_substitution_arrow() {
        let ty = PolyType::Arrow(
            Box::new(PolyType::Var("a".to_string())),
            Box::new(PolyType::Var("b".to_string())),
        );
        let subst = TypeSubst::new()
            .bind("a".to_string(), PolyType::Int)
            .bind("b".to_string(), PolyType::Bool);
        let result = subst.apply(&ty);
        
        let expected = PolyType::Arrow(
            Box::new(PolyType::Int),
            Box::new(PolyType::Bool),
        );
        assert_eq!(result, expected);
    }

    #[test]
    fn test_type_substitution_list() {
        let ty = PolyType::List(Box::new(PolyType::Var("a".to_string())));
        let subst = TypeSubst::new().bind("a".to_string(), PolyType::Int);
        let result = subst.apply(&ty);
        
        let expected = PolyType::List(Box::new(PolyType::Int));
        assert_eq!(result, expected);
    }
}

fn main() {
    println!("Arrow Calculus: Challenge #3 - Polymorphic Arrow Types");
    println!("======================================================\n");

    // Experiment 1: Identity polymorphism
    println!("Experiment 1: Polymorphic Identity");
    println!("  General type: {}", poly_identity_type());
    println!("  Instantiated at Int: {}", poly_identity_at_int());
    println!("  Instantiated at [Int]: {}\n", poly_identity_at_list_int());

    // Experiment 2: Const polymorphism
    println!("Experiment 2: Polymorphic Const");
    println!("  General type: {}", poly_const_type());
    println!("  Instantiated at Int, Bool: {}\n", poly_const_at_int_bool());

    // Experiment 3: Compose polymorphism
    println!("Experiment 3: Polymorphic Composition");
    println!("  General type: {}", poly_compose_type());
    println!("  Instantiated at Int -> String -> Bool: {}\n", poly_compose_at_int_string_bool());

    // Experiment 4: Map polymorphism
    println!("Experiment 4: Polymorphic Map");
    println!("  General type: {}", poly_map_type());
    println!("  Instantiated at Int -> Bool: {}\n", poly_map_at_int_bool());

    // Experiment 5: Fold polymorphism
    println!("Experiment 5: Polymorphic Fold");
    println!("  General type: {}", poly_fold_type());
    println!("  Instantiated at Int elements, Bool accumulator: {}\n", poly_fold_at_int_bool());

    // Type substitution test
    println!("Test: Type Substitution");
    let arrow_type = PolyType::Arrow(
        Box::new(PolyType::Var("a".to_string())),
        Box::new(PolyType::Var("b".to_string())),
    );
    println!("  Original: {}", arrow_type);
    let subst = TypeSubst::new()
        .bind("a".to_string(), PolyType::Int)
        .bind("b".to_string(), PolyType::Bool);
    println!("  After substituting a -> Int, b -> Bool: {}\n", subst.apply(&arrow_type));
}
