// Arrow Calculus PoC: Core Implementation
// Implements the formalism defined in FORMALISM.md

use std::fmt;
use std::collections::HashMap;

// ============================================================================
// Type System
// ============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Var(String),
    Int,
    Bool,
    String,
    Unit,
    Product(Box<Type>, Box<Type>),
    Sum(Box<Type>, Box<Type>),
    List(Box<Type>),
    Function(Box<Type>, Box<Type>),  // τ → σ
    Arrow(Box<Type>, Box<Type>),      // τ ~> σ
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Var(n) => write!(f, "{}", n),
            Type::Int => write!(f, "Int"),
            Type::Bool => write!(f, "Bool"),
            Type::String => write!(f, "String"),
            Type::Unit => write!(f, "()"),
            Type::Product(a, b) => write!(f, "({} × {})", a, b),
            Type::Sum(a, b) => write!(f, "({} + {})", a, b),
            Type::List(t) => write!(f, "[{}]", t),
            Type::Function(a, b) => write!(f, "{} → {}", a, b),
            Type::Arrow(a, b) => write!(f, "{} ~> {}", a, b),
        }
    }
}

// ============================================================================
// Values
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i32),
    Bool(bool),
    String(String),
    Unit,
    Product(Box<Value>, Box<Value>),
    Left(Box<Value>),
    Right(Box<Value>),
    List(Vec<Value>),
    Arrow(ArrowValue),
    Closure {
        param: String,
        body: Expr,
        env: Environment,
    },
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Int(n) => write!(f, "{}", n),
            Value::Bool(b) => write!(f, "{}", b),
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::Unit => write!(f, "()"),
            Value::Product(a, b) => write!(f, "({}, {})", a, b),
            Value::Left(v) => write!(f, "Left({})", v),
            Value::Right(v) => write!(f, "Right({})", v),
            Value::List(vs) => {
                write!(f, "[")?;
                for (i, v) in vs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, "]")
            }
            Value::Arrow(_) => write!(f, "<arrow>"),
            Value::Closure { .. } => write!(f, "<closure>"),
        }
    }
}

// ============================================================================
// Arrow Values
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
pub enum ArrowValue {
    Arr(Box<Value>),                           // lift function
    Comp(Box<ArrowValue>, Box<ArrowValue>),    // f >>> g
    First(Box<ArrowValue>),                    // first f
    Choice(Box<ArrowValue>, Box<ArrowValue>),  // choice f g
    Loop(Box<ArrowValue>),                     // loop f
}

// ============================================================================
// AST
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Var(String),
    Lit(Box<Value>),
    Arr(Box<Expr>),
    Comp(Box<Expr>, Box<Expr>),
    First(Box<Expr>),
    Choice(Box<Expr>, Box<Expr>),
    Loop(Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    BinOp(String, Box<Expr>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Lambda(String, Box<Expr>),
    Let(String, Box<Expr>, Box<Expr>),
}

// ============================================================================
// Environment
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
pub struct Environment {
    bindings: HashMap<String, Value>,
}

impl Environment {
    pub fn new() -> Self {
        Environment {
            bindings: HashMap::new(),
        }
    }

    pub fn extend(&self, name: String, value: Value) -> Self {
        let mut bindings = self.bindings.clone();
        bindings.insert(name, value);
        Environment { bindings }
    }

    pub fn get(&self, name: &str) -> Option<Value> {
        self.bindings.get(name).cloned()
    }
}

// ============================================================================
// Evaluation
// ============================================================================

#[derive(Debug)]
pub enum EvalError {
    UnboundVariable(String),
    NotAFunction(String),
    ExpectedInt(String),
    ExpectedBool(String),
    ExpectedArrow(String),
    ExpectedProduct(String),
    ExpectedSum(String),
    TypeMismatch(String, String),
    RuntimeError(String),
}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EvalError::UnboundVariable(name) => write!(f, "Unbound variable: {}", name),
            EvalError::NotAFunction(msg) => write!(f, "Not a function: {}", msg),
            EvalError::ExpectedInt(msg) => write!(f, "Expected Int: {}", msg),
            EvalError::ExpectedBool(msg) => write!(f, "Expected Bool: {}", msg),
            EvalError::ExpectedArrow(msg) => write!(f, "Expected Arrow: {}", msg),
            EvalError::ExpectedProduct(msg) => write!(f, "Expected Product: {}", msg),
            EvalError::ExpectedSum(msg) => write!(f, "Expected Sum: {}", msg),
            EvalError::TypeMismatch(a, b) => write!(f, "Type mismatch: {} vs {}", a, b),
            EvalError::RuntimeError(msg) => write!(f, "Runtime error: {}", msg),
        }
    }
}

pub fn eval(env: &Environment, expr: &Expr) -> Result<Value, EvalError> {
    match expr {
        Expr::Lit(v) => Ok((**v).clone()),
        
        Expr::Var(name) => {
            env.get(name)
                .ok_or_else(|| EvalError::UnboundVariable(name.clone()))
        }
        
        Expr::Arr(e) => {
            let v = eval(env, e)?;
            Ok(Value::Arrow(ArrowValue::Arr(Box::new(v))))
        }
        
        Expr::Comp(f, g) => {
            let vf = eval(env, f)?;
            let vg = eval(env, g)?;
            match (vf, vg) {
                (Value::Arrow(af), Value::Arrow(ag)) => {
                    Ok(Value::Arrow(ArrowValue::Comp(Box::new(af), Box::new(ag))))
                }
                _ => Err(EvalError::ExpectedArrow("composition requires arrows".to_string())),
            }
        }
        
        Expr::First(e) => {
            let v = eval(env, e)?;
            match v {
                Value::Arrow(a) => Ok(Value::Arrow(ArrowValue::First(Box::new(a)))),
                _ => Err(EvalError::ExpectedArrow("first requires an arrow".to_string())),
            }
        }
        
        Expr::Choice(f, g) => {
            let vf = eval(env, f)?;
            let vg = eval(env, g)?;
            match (vf, vg) {
                (Value::Arrow(af), Value::Arrow(ag)) => {
                    Ok(Value::Arrow(ArrowValue::Choice(Box::new(af), Box::new(ag))))
                }
                _ => Err(EvalError::ExpectedArrow("choice requires arrows".to_string())),
            }
        }
        
        Expr::Loop(e) => {
            let v = eval(env, e)?;
            match v {
                Value::Arrow(a) => Ok(Value::Arrow(ArrowValue::Loop(Box::new(a)))),
                _ => Err(EvalError::ExpectedArrow("loop requires an arrow".to_string())),
            }
        }
        
        Expr::Lambda(param, body) => {
            Ok(Value::Closure {
                param: param.clone(),
                body: (**body).clone(),
                env: env.clone(),
            })
        }
        
        Expr::App(f, arg) => {
            let func = eval(env, f)?;
            let value = eval(env, arg)?;
            
            match func {
                Value::Closure { param, body, env: closure_env } => {
                    let new_env = closure_env.extend(param, value);
                    eval(&new_env, &body)
                }
                _ => Err(EvalError::NotAFunction(format!("{:?}", func))),
            }
        }
        
        Expr::BinOp(op, e1, e2) => {
            let v1 = eval(env, e1)?;
            let v2 = eval(env, e2)?;
            eval_binop(op, v1, v2)
        }
        
        Expr::If(cond, then_e, else_e) => {
            let cond_v = eval(env, cond)?;
            match cond_v {
                Value::Bool(b) => {
                    if b {
                        eval(env, then_e)
                    } else {
                        eval(env, else_e)
                    }
                }
                _ => Err(EvalError::ExpectedBool("if condition".to_string())),
            }
        }
        
        Expr::Let(name, e, body) => {
            let v = eval(env, e)?;
            let new_env = env.extend(name.clone(), v);
            eval(&new_env, body)
        }
    }
}

fn eval_binop(op: &str, v1: Value, v2: Value) -> Result<Value, EvalError> {
    match op {
        "+" => match (v1, v2) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a + b)),
            _ => Err(EvalError::ExpectedInt("+ operand".to_string())),
        },
        "-" => match (v1, v2) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a - b)),
            _ => Err(EvalError::ExpectedInt("- operand".to_string())),
        },
        "*" => match (v1, v2) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a * b)),
            _ => Err(EvalError::ExpectedInt("* operand".to_string())),
        },
        "/" => match (v1, v2) {
            (Value::Int(_a), Value::Int(0)) => Err(EvalError::RuntimeError("division by zero".to_string())),
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a / b)),
            _ => Err(EvalError::ExpectedInt("/ operand".to_string())),
        },
        "<" => match (v1, v2) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a < b)),
            _ => Err(EvalError::ExpectedInt("< operand".to_string())),
        },
        "<=" => match (v1, v2) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a <= b)),
            _ => Err(EvalError::ExpectedInt("<= operand".to_string())),
        },
        ">" => match (v1, v2) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a > b)),
            _ => Err(EvalError::ExpectedInt("> operand".to_string())),
        },
        ">=" => match (v1, v2) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a >= b)),
            _ => Err(EvalError::ExpectedInt(">= operand".to_string())),
        },
        "==" => {
            // Structural equality
            Ok(Value::Bool(v1 == v2))
        },
        "pair" => Ok(Value::Product(Box::new(v1), Box::new(v2))),
        _ => Err(EvalError::RuntimeError(format!("Unknown operator: {}", op))),
    }
}

// ============================================================================
// Arrow Execution
// ============================================================================

pub fn run_arrow(arrow: &ArrowValue, input: Value, max_iterations: usize) -> Result<Value, EvalError> {
    match arrow {
        ArrowValue::Arr(v) => {
            // Apply function to input
            match v.as_ref() {
                Value::Closure { param, body, env } => {
                    let new_env = env.extend(param.clone(), input);
                    eval(&new_env, body)
                }
                _ => Err(EvalError::NotAFunction("arr requires a function".to_string())),
            }
        }
        
        ArrowValue::Comp(af, ag) => {
            let intermediate = run_arrow(af, input, max_iterations)?;
            run_arrow(ag, intermediate, max_iterations)
        }
        
        ArrowValue::First(af) => {
            match input {
                Value::Product(a, b) => {
                    let a_out = run_arrow(af, *a, max_iterations)?;
                    Ok(Value::Product(Box::new(a_out), b))
                }
                _ => Err(EvalError::ExpectedProduct("first requires a product".to_string())),
            }
        }
        
        ArrowValue::Choice(af, ag) => {
            match input {
                Value::Left(v) => run_arrow(af, *v, max_iterations),
                Value::Right(v) => run_arrow(ag, *v, max_iterations),
                _ => Err(EvalError::ExpectedSum("choice requires a sum".to_string())),
            }
        }
        
        ArrowValue::Loop(step) => {
            // State machine loop with iteration limit
            // For now, we assume input is the initial state
            loop_iterate(step, input, Value::Unit, max_iterations)
        }
    }
}

fn loop_iterate(
    step: &ArrowValue,
    mut current_value: Value,
    mut state: Value,
    mut iterations: usize,
) -> Result<Value, EvalError> {
    // Initialize state if needed
    if matches!(state, Value::Unit) {
        state = Value::Int(0); // Default initial state
    }
    
    while iterations > 0 {
        iterations -= 1;
        
        // Create input: (value, state)
        let step_input = Value::Product(Box::new(current_value.clone()), Box::new(state.clone()));
        
        // Run step
        let result = run_arrow(step, step_input, iterations)?;
        
        // Expect output: (value, state)
        match result {
            Value::Product(val_out, state_out) => {
                // Check for termination (state unchanged)
                if *state_out == state {
                    return Ok(*val_out);
                }
                current_value = *val_out;
                state = *state_out;
            }
            _ => return Err(EvalError::ExpectedProduct("loop step must return product".to_string())),
        }
    }
    
    Err(EvalError::RuntimeError("loop exceeded iteration limit".to_string()))
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn env() -> Environment {
        Environment::new()
    }

    #[test]
    fn test_identity() {
        // id = arr (λx. x)
        let id = Expr::Arr(Box::new(Expr::Lambda(
            "x".to_string(),
            Box::new(Expr::Var("x".to_string())),
        )));
        
        let env = env();
        let result = eval(&env, &id).unwrap();
        
        match result {
            Value::Arrow(ArrowValue::Arr(_)) => {
                // Try running it
                match run_arrow(&ArrowValue::Arr(Box::new(Value::Closure {
                    param: "x".to_string(),
                    body: Expr::Var("x".to_string()),
                    env: env.clone(),
                })), Value::Int(5), 100) {
                    Ok(Value::Int(5)) => {}
                    other => panic!("Expected Int(5), got {:?}", other),
                }
            }
            _ => panic!("Expected arrow, got {:?}", result),
        }
    }

    #[test]
    fn test_increment() {
        // add1 = arr (λx. x + 1)
        let add1 = Expr::Arr(Box::new(Expr::Lambda(
            "x".to_string(),
            Box::new(Expr::BinOp(
                "+".to_string(),
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::Lit(Box::new(Value::Int(1)))),
            )),
        )));
        
        let env = env();
        let result = eval(&env, &add1).unwrap();
        
        match result {
            Value::Arrow(ArrowValue::Arr(closure_val)) => {
                match run_arrow(&ArrowValue::Arr(closure_val), Value::Int(5), 100) {
                    Ok(Value::Int(6)) => {}
                    other => panic!("Expected Int(6), got {:?}", other),
                }
            }
            _ => panic!("Expected arrow, got {:?}", result),
        }
    }

    #[test]
    fn test_composition() {
        // add1 = arr (λx. x + 1)
        // mul2 = arr (λx. x * 2)
        // composed = add1 >>> mul2
        
        let add1 = Expr::Arr(Box::new(Expr::Lambda(
            "x".to_string(),
            Box::new(Expr::BinOp(
                "+".to_string(),
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::Lit(Box::new(Value::Int(1)))),
            )),
        )));
        
        let mul2 = Expr::Arr(Box::new(Expr::Lambda(
            "x".to_string(),
            Box::new(Expr::BinOp(
                "*".to_string(),
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::Lit(Box::new(Value::Int(2)))),
            )),
        )));
        
        let composed = Expr::Comp(Box::new(add1), Box::new(mul2));
        
        let env = env();
        let result = eval(&env, &composed).unwrap();
        
        match result {
            Value::Arrow(arrow_val) => {
                match run_arrow(&arrow_val, Value::Int(5), 100) {
                    Ok(Value::Int(12)) => {} // (5+1)*2 = 12
                    other => panic!("Expected Int(12), got {:?}", other),
                }
            }
            _ => panic!("Expected arrow, got {:?}", result),
        }
    }
}

fn main() {
    println!("Arrow Calculus PoC");
    println!("==================\n");
    
    // Test: Identity
    println!("Test 1: Identity");
    let id = Expr::Arr(Box::new(Expr::Lambda(
        "x".to_string(),
        Box::new(Expr::Var("x".to_string())),
    )));
    let env = Environment::new();
    match eval(&env, &id) {
        Ok(val) => println!("  Result: {}\n", val),
        Err(e) => println!("  Error: {}\n", e),
    }
    
    // Test: Increment
    println!("Test 2: Increment");
    let add1 = Expr::Arr(Box::new(Expr::Lambda(
        "x".to_string(),
        Box::new(Expr::BinOp(
            "+".to_string(),
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Lit(Box::new(Value::Int(1)))),
        )),
    )));
    match eval(&env, &add1) {
        Ok(Value::Arrow(arrow_val)) => {
            match run_arrow(&arrow_val, Value::Int(5), 100) {
                Ok(result) => println!("  Result: {}\n", result),
                Err(e) => println!("  Error: {}\n", e),
            }
        }
        other => println!("  Error: {:?}\n", other),
    }
    
    // Test: Composition
    println!("Test 3: Composition (add1 >>> mul2)");
    let add1 = Expr::Arr(Box::new(Expr::Lambda(
        "x".to_string(),
        Box::new(Expr::BinOp(
            "+".to_string(),
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Lit(Box::new(Value::Int(1)))),
        )),
    )));
    
    let mul2 = Expr::Arr(Box::new(Expr::Lambda(
        "x".to_string(),
        Box::new(Expr::BinOp(
            "*".to_string(),
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Lit(Box::new(Value::Int(2)))),
        )),
    )));
    
    let composed = Expr::Comp(Box::new(add1), Box::new(mul2));
    
    match eval(&env, &composed) {
        Ok(Value::Arrow(arrow_val)) => {
            match run_arrow(&arrow_val, Value::Int(5), 100) {
                Ok(result) => println!("  Result: {} (expected 12)\n", result),
                Err(e) => println!("  Error: {}\n", e),
            }
        }
        other => println!("  Error: {:?}\n", other),
    }
}
