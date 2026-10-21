// Challenge #4: Typing via Hindley-Milner Inference
// Tests for type inference on arrow expressions
//
// Key questions:
// 1. Can we infer types for arrow expressions without explicit annotations?
// 2. Does Hindley-Milner unification work for arrow types?
// 3. Can we infer the principal type (most general type)?

use std::collections::HashMap;
use std::fmt;

// ============================================================================
// Type System
// ============================================================================

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Int,
    Bool,
    Unit,
    Var(String),                       // Type variable (e.g., 'a')
    Arrow(Box<Type>, Box<Type>),       // a ~> b
    List(Box<Type>),                   // [a]
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Int => write!(f, "Int"),
            Type::Bool => write!(f, "Bool"),
            Type::Unit => write!(f, "()"),
            Type::Var(name) => write!(f, "{}", name),
            Type::Arrow(a, b) => write!(f, "{} ~> {}", a, b),
            Type::List(t) => write!(f, "[{}]", t),
        }
    }
}

// ============================================================================
// Substitution (Type Variable Bindings)
// ============================================================================

#[derive(Debug, Clone, Default)]
pub struct Substitution {
    bindings: HashMap<String, Type>,
}

impl Substitution {
    pub fn new() -> Self {
        Substitution {
            bindings: HashMap::new(),
        }
    }

    pub fn insert(&mut self, var: String, ty: Type) {
        self.bindings.insert(var, ty);
    }

    pub fn get(&self, var: &str) -> Option<&Type> {
        self.bindings.get(var)
    }

    pub fn apply(&self, ty: &Type) -> Type {
        match ty {
            Type::Var(name) => {
                match self.get(name) {
                    Some(t) => self.apply(t),
                    None => ty.clone(),
                }
            }
            Type::Arrow(a, b) => {
                Type::Arrow(
                    Box::new(self.apply(a)),
                    Box::new(self.apply(b)),
                )
            }
            Type::List(t) => Type::List(Box::new(self.apply(t))),
            other => other.clone(),
        }
    }

    pub fn compose(&self, other: &Substitution) -> Substitution {
        let mut result = self.clone();
        for (var, ty) in &other.bindings {
            result.insert(var.clone(), self.apply(ty));
        }
        result
    }
}

// ============================================================================
// Unification (Constraint Solving)
// ============================================================================

pub struct Unifier;

impl Unifier {
    /// Unify two types; returns a substitution if successful
    pub fn unify(ty1: &Type, ty2: &Type) -> Option<Substitution> {
        let mut subst = Substitution::new();
        if Unifier::unify_with_subst(ty1, ty2, &mut subst) {
            Some(subst)
        } else {
            None
        }
    }

    fn unify_with_subst(ty1: &Type, ty2: &Type, subst: &mut Substitution) -> bool {
        let ty1 = subst.apply(ty1);
        let ty2 = subst.apply(ty2);

        match (&ty1, &ty2) {
            // Same types unify
            (Type::Int, Type::Int) => true,
            (Type::Bool, Type::Bool) => true,
            (Type::Unit, Type::Unit) => true,

            // Variable unifies with anything (occurs check would go here)
            (Type::Var(a), Type::Var(b)) if a == b => true,
            (Type::Var(a), b) => {
                if Unifier::occurs_in(a, b) {
                    false  // Occurs check fails
                } else {
                    subst.insert(a.clone(), b.clone());
                    true
                }
            }
            (a, Type::Var(b)) => {
                if Unifier::occurs_in(b, a) {
                    false
                } else {
                    subst.insert(b.clone(), a.clone());
                    true
                }
            }

            // Arrow types unify component-wise
            (Type::Arrow(a1, b1), Type::Arrow(a2, b2)) => {
                Unifier::unify_with_subst(a1, a2, subst)
                    && Unifier::unify_with_subst(b1, b2, subst)
            }

            // List types unify element-wise
            (Type::List(t1), Type::List(t2)) => {
                Unifier::unify_with_subst(t1, t2, subst)
            }

            // No unification
            _ => false,
        }
    }

    /// Occurs check: does variable occur in type?
    fn occurs_in(var: &str, ty: &Type) -> bool {
        match ty {
            Type::Var(v) => v == var,
            Type::Arrow(a, b) => Unifier::occurs_in(var, a) || Unifier::occurs_in(var, b),
            Type::List(t) => Unifier::occurs_in(var, t),
            _ => false,
        }
    }
}

// ============================================================================
// Constraints (Generated during type checking)
// ============================================================================

#[derive(Debug, Clone)]
pub struct Constraint {
    pub ty1: Type,
    pub ty2: Type,
}

// ============================================================================
// Simple Arrow Expression Language
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
pub enum ArrowExpr {
    // Literals
    IntLit(i32),
    BoolLit(bool),

    // Arrow primitives
    Identity,                              // arr id
    Constant(Box<ArrowExpr>),              // const (value)
    Add,                                   // arr (+)
    Multiply,                              // arr (*)
    IsEven,                                // arr (λx. x % 2 == 0)

    // Combinators
    Compose(Box<ArrowExpr>, Box<ArrowExpr>), // f >>> g
    Map(Box<ArrowExpr>),                   // map f [xs]
    Fold(Box<ArrowExpr>),                  // fold f [xs]

    // Variable reference
    Var(String),
}

// ============================================================================
// Type Inference Engine
// ============================================================================

pub struct TypeInference {
    next_var_id: usize,
}

impl TypeInference {
    pub fn new() -> Self {
        TypeInference { next_var_id: 0 }
    }

    fn fresh_var(&mut self) -> Type {
        let name = format!("t{}", self.next_var_id);
        self.next_var_id += 1;
        Type::Var(name)
    }

    /// Infer the type of an arrow expression
    pub fn infer(&mut self, expr: &ArrowExpr) -> Result<Type, String> {
        let (_ty, constraints) = self.infer_with_constraints(expr)?;
        let subst = self.solve_constraints(constraints)?;
        Ok(subst.apply(&_ty))
    }

    /// Infer type and collect constraints
    fn infer_with_constraints(&mut self, expr: &ArrowExpr) -> Result<(Type, Vec<Constraint>), String> {
        let mut constraints = Vec::new();

        let ty = match expr {
            // Integer literal: Int
            ArrowExpr::IntLit(_) => Type::Int,

            // Boolean literal: Bool
            ArrowExpr::BoolLit(_) => Type::Bool,

            // Identity: forall a. a ~> a
            ArrowExpr::Identity => {
                let a = self.fresh_var();
                Type::Arrow(Box::new(a.clone()), Box::new(a))
            }

            // Addition: Int ~> Int ~> Int
            ArrowExpr::Add => {
                Type::Arrow(
                    Box::new(Type::Int),
                    Box::new(Type::Arrow(
                        Box::new(Type::Int),
                        Box::new(Type::Int),
                    )),
                )
            }

            // Multiplication: Int ~> Int ~> Int
            ArrowExpr::Multiply => {
                Type::Arrow(
                    Box::new(Type::Int),
                    Box::new(Type::Arrow(
                        Box::new(Type::Int),
                        Box::new(Type::Int),
                    )),
                )
            }

            // IsEven: Int ~> Bool
            ArrowExpr::IsEven => {
                Type::Arrow(Box::new(Type::Int), Box::new(Type::Bool))
            }

            // Compose: (a ~> b) ~> (b ~> c) ~> (a ~> c)
            ArrowExpr::Compose(f, g) => {
                let (f_ty, mut f_constraints) = self.infer_with_constraints(f)?;
                let (g_ty, g_constraints) = self.infer_with_constraints(g)?;

                let a = self.fresh_var();
                let b = self.fresh_var();
                let c = self.fresh_var();

                // f should have type a ~> b
                constraints.push(Constraint {
                    ty1: f_ty,
                    ty2: Type::Arrow(Box::new(a.clone()), Box::new(b.clone())),
                });

                // g should have type b ~> c
                constraints.push(Constraint {
                    ty1: g_ty,
                    ty2: Type::Arrow(Box::new(b), Box::new(c.clone())),
                });

                constraints.append(&mut f_constraints);
                constraints.extend(g_constraints);

                Type::Arrow(Box::new(a), Box::new(c))
            }

            // Map: (a ~> b) ~> ([a] ~> [b])
            ArrowExpr::Map(f) => {
                let (f_ty, f_constraints) = self.infer_with_constraints(f)?;

                let a = self.fresh_var();
                let b = self.fresh_var();

                constraints.push(Constraint {
                    ty1: f_ty,
                    ty2: Type::Arrow(Box::new(a.clone()), Box::new(b.clone())),
                });

                constraints.extend(f_constraints);

                Type::Arrow(
                    Box::new(Type::List(Box::new(a))),
                    Box::new(Type::List(Box::new(b))),
                )
            }

            // Fold: (b ~> (a ~> b)) ~> (b ~> ([a] ~> b))
            ArrowExpr::Fold(f) => {
                let (f_ty, f_constraints) = self.infer_with_constraints(f)?;

                let a = self.fresh_var();
                let b = self.fresh_var();

                constraints.push(Constraint {
                    ty1: f_ty,
                    ty2: Type::Arrow(
                        Box::new(b.clone()),
                        Box::new(Type::Arrow(Box::new(a.clone()), Box::new(b.clone()))),
                    ),
                });

                constraints.extend(f_constraints);

                Type::Arrow(
                    Box::new(b.clone()),
                    Box::new(Type::Arrow(
                        Box::new(Type::List(Box::new(a))),
                        Box::new(b),
                    )),
                )
            }

            ArrowExpr::Constant(_) => self.fresh_var(),
            ArrowExpr::Var(_) => self.fresh_var(),
        };

        Ok((ty, constraints))
    }

    /// Solve constraints via unification
    fn solve_constraints(&self, constraints: Vec<Constraint>) -> Result<Substitution, String> {
        let mut subst = Substitution::new();

        for constraint in constraints {
            let ty1 = subst.apply(&constraint.ty1);
            let ty2 = subst.apply(&constraint.ty2);

            match Unifier::unify(&ty1, &ty2) {
                Some(unif) => subst = subst.compose(&unif),
                None => {
                    return Err(format!(
                        "Type mismatch: {} does not unify with {}",
                        ty1, ty2
                    ))
                }
            }
        }

        Ok(subst)
    }
}

// ============================================================================
// Test Suite
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unify_same_types() {
        let t1 = Type::Int;
        let t2 = Type::Int;
        assert!(Unifier::unify(&t1, &t2).is_some());
    }

    #[test]
    fn test_unify_var_to_type() {
        let t1 = Type::Var("a".to_string());
        let t2 = Type::Int;
        let subst = Unifier::unify(&t1, &t2).unwrap();
        assert_eq!(subst.apply(&Type::Var("a".to_string())), Type::Int);
    }

    #[test]
    fn test_unify_arrow_types() {
        let t1 = Type::Arrow(Box::new(Type::Var("a".to_string())), Box::new(Type::Int));
        let t2 = Type::Arrow(Box::new(Type::Bool), Box::new(Type::Int));
        let subst = Unifier::unify(&t1, &t2).unwrap();
        assert_eq!(subst.apply(&Type::Var("a".to_string())), Type::Bool);
    }

    #[test]
    fn test_unify_list_types() {
        let t1 = Type::List(Box::new(Type::Var("a".to_string())));
        let t2 = Type::List(Box::new(Type::Int));
        let subst = Unifier::unify(&t1, &t2).unwrap();
        assert_eq!(subst.apply(&Type::Var("a".to_string())), Type::Int);
    }

    #[test]
    fn test_unify_incompatible() {
        let t1 = Type::Int;
        let t2 = Type::Bool;
        assert!(Unifier::unify(&t1, &t2).is_none());
    }

    #[test]
    fn test_infer_int_literal() {
        let mut inf = TypeInference::new();
        let expr = ArrowExpr::IntLit(42);
        let ty = inf.infer(&expr).unwrap();
        assert_eq!(ty, Type::Int);
    }

    #[test]
    fn test_infer_bool_literal() {
        let mut inf = TypeInference::new();
        let expr = ArrowExpr::BoolLit(true);
        let ty = inf.infer(&expr).unwrap();
        assert_eq!(ty, Type::Bool);
    }

    #[test]
    fn test_infer_identity() {
        let mut inf = TypeInference::new();
        let expr = ArrowExpr::Identity;
        let ty = inf.infer(&expr).unwrap();
        // Should be a ~> a (polymorphic)
        match ty {
            Type::Arrow(a, b) => assert_eq!(a, b),
            _ => panic!("Expected arrow type"),
        }
    }

    #[test]
    fn test_infer_add() {
        let mut inf = TypeInference::new();
        let expr = ArrowExpr::Add;
        let ty = inf.infer(&expr).unwrap();
        // Should be Int ~> Int ~> Int
        assert_eq!(
            ty,
            Type::Arrow(
                Box::new(Type::Int),
                Box::new(Type::Arrow(Box::new(Type::Int), Box::new(Type::Int)))
            )
        );
    }

    #[test]
    fn test_infer_is_even() {
        let mut inf = TypeInference::new();
        let expr = ArrowExpr::IsEven;
        let ty = inf.infer(&expr).unwrap();
        // Should be Int ~> Bool
        assert_eq!(ty, Type::Arrow(Box::new(Type::Int), Box::new(Type::Bool)));
    }

    #[test]
    fn test_infer_compose() {
        let mut inf = TypeInference::new();
        let id = Box::new(ArrowExpr::Identity);
        let is_even = Box::new(ArrowExpr::IsEven);
        let expr = ArrowExpr::Compose(id, is_even);
        let ty = inf.infer(&expr).unwrap();
        // Identity >>> IsEven should be Int ~> Bool
        assert_eq!(ty, Type::Arrow(Box::new(Type::Int), Box::new(Type::Bool)));
    }

    #[test]
    fn test_infer_map() {
        let mut inf = TypeInference::new();
        let f = Box::new(ArrowExpr::IsEven);
        let expr = ArrowExpr::Map(f);
        let ty = inf.infer(&expr).unwrap();
        // Map IsEven should be [Int] ~> [Bool]
        assert_eq!(
            ty,
            Type::Arrow(
                Box::new(Type::List(Box::new(Type::Int))),
                Box::new(Type::List(Box::new(Type::Bool)))
            )
        );
    }

    #[test]
    fn test_infer_fold() {
        let mut inf = TypeInference::new();
        let f = Box::new(ArrowExpr::Add);
        let expr = ArrowExpr::Fold(f);
        let ty = inf.infer(&expr).unwrap();
        // Fold Add should infer correct type
        match ty {
            Type::Arrow(_, inner) => match *inner {
                Type::Arrow(_, _) => {
                    // Structure is correct (higher-order)
                }
                _ => panic!("Inner arrow expected"),
            },
            _ => panic!("Arrow type expected"),
        }
    }

    #[test]
    fn test_substitution_apply() {
        let mut subst = Substitution::new();
        subst.insert("a".to_string(), Type::Int);
        let ty = Type::Var("a".to_string());
        assert_eq!(subst.apply(&ty), Type::Int);
    }

    #[test]
    fn test_substitution_compose() {
        let mut s1 = Substitution::new();
        s1.insert("a".to_string(), Type::Var("b".to_string()));

        let mut s2 = Substitution::new();
        s2.insert("b".to_string(), Type::Int);

        let composed = s1.compose(&s2);
        assert_eq!(composed.apply(&Type::Var("a".to_string())), Type::Int);
    }
}

fn main() {
    println!("Arrow Calculus: Challenge #4 - Hindley-Milner Type Inference");
    println!("============================================================\n");

    let mut inf = TypeInference::new();

    // Test 1: Identity
    println!("Test 1: Identity (forall a. a ~> a)");
    let ty = inf.infer(&ArrowExpr::Identity).unwrap();
    println!("  Inferred type: {}\n", ty);

    // Test 2: Add
    println!("Test 2: Add (Int ~> Int ~> Int)");
    let ty = inf.infer(&ArrowExpr::Add).unwrap();
    println!("  Inferred type: {}\n", ty);

    // Test 3: IsEven
    println!("Test 3: IsEven (Int ~> Bool)");
    let ty = inf.infer(&ArrowExpr::IsEven).unwrap();
    println!("  Inferred type: {}\n", ty);

    // Test 4: Compose
    println!("Test 4: Identity >>> IsEven");
    let expr = ArrowExpr::Compose(
        Box::new(ArrowExpr::Identity),
        Box::new(ArrowExpr::IsEven),
    );
    let ty = inf.infer(&expr).unwrap();
    println!("  Inferred type: {} (should be Int ~> Bool)\n", ty);

    // Test 5: Map
    println!("Test 5: Map IsEven");
    let expr = ArrowExpr::Map(Box::new(ArrowExpr::IsEven));
    let ty = inf.infer(&expr).unwrap();
    println!("  Inferred type: {} (should be [Int] ~> [Bool])\n", ty);

    // Test 6: Fold
    println!("Test 6: Fold Add");
    let expr = ArrowExpr::Fold(Box::new(ArrowExpr::Add));
    let ty = inf.infer(&expr).unwrap();
    println!("  Inferred type: {}\n", ty);

    // Test 7: Unification examples
    println!("Test 7: Unification");
    let t1 = Type::Arrow(
        Box::new(Type::Var("a".to_string())),
        Box::new(Type::Int),
    );
    let t2 = Type::Arrow(Box::new(Type::Bool), Box::new(Type::Int));
    if let Some(subst) = Unifier::unify(&t1, &t2) {
        println!("  Unified: a = {}", subst.apply(&Type::Var("a".to_string())));
    }
}
