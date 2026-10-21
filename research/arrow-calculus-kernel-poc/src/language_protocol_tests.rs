// Challenge #7: First-class Language Protocol
// Challenge #8: Generic Language-Agnostic Tooling
//
// Key questions:
// 1. Can a programming language be modelled as a protocol whose every
//    operation (parse, eval, format, typecheck) is an *arrow*?
// 2. Because arrows compose, can a single generic tool (pretty-printer,
//    error reporter, optimizer) be written once and run unchanged over ANY
//    language instance — differing only in the Language parameter?
//
// Model: a `Language` is a record of arrows (`Rc<dyn Fn(Value) -> Comp>`),
// reusing the freer-arrow + handler machinery from Phase 2. Each language
// instance supplies its own parse/eval/format/typecheck/lit arrows. Generic
// tools are functions `&Language -> ...` that build arrow pipelines from the
// language's arrows; the SAME tool code runs against every language.

use std::fmt;
use std::rc::Rc;

// ============================================================================
// Values
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i32),
    Bool(bool),
    Str(String),
    Unit,
    Product(Box<Value>, Box<Value>),
    List(Vec<Value>),
    Left(Box<Value>),
    Right(Box<Value>),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Int(n) => write!(f, "{}", n),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Str(s) => write!(f, "\"{}\"", s),
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
        }
    }
}

impl Value {
    fn as_int(&self) -> Option<i32> {
        match self {
            Value::Int(n) => Some(*n),
            _ => None,
        }
    }

    fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }

    fn as_str(&self) -> Option<&str> {
        match self {
            Value::Str(s) => Some(s),
            _ => None,
        }
    }
}

// ============================================================================
// Effect Operations & Freer Arrow (minimal, reused from Phase 2)
// ============================================================================
//
// Only the Exception effect is needed here (parse/eval/typecheck raise errors
// via `throw`; tools catch them via `handle_exception`). The full Op enum is
// retained to match the Phase 2 model; unused variants are allowed.

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Op {
    Get,
    Put,
    Read,
    Write,
    Throw,
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Op::Get => write!(f, "Get"),
            Op::Put => write!(f, "Put"),
            Op::Read => write!(f, "Read"),
            Op::Write => write!(f, "Write"),
            Op::Throw => write!(f, "Throw"),
        }
    }
}

pub enum Comp {
    Pure(Value),
    Op(Op, Value, Rc<dyn Fn(Value) -> Comp + 'static>),
}

pub fn pure(v: Value) -> Comp {
    Comp::Pure(v)
}

/// `arr f`: lift a pure function `f : Value -> Value` into an arrow
/// `Value ~> Value` (a pure computation-producing arrow).
pub fn arr(f: fn(Value) -> Value) -> Rc<dyn Fn(Value) -> Comp + 'static> {
    Rc::new(move |x| pure(f(x)))
}

/// Monadic bind / arrow sequencing: thread `g` onto every continuation of `f`.
pub fn bind(comp: Comp, g: Rc<dyn Fn(Value) -> Comp + 'static>) -> Comp {
    match comp {
        Comp::Pure(v) => g(v),
        Comp::Op(op, arg, k) => {
            let g2 = Rc::clone(&g);
            Comp::Op(op, arg, Rc::new(move |r| bind(k(r), Rc::clone(&g2))))
        }
    }
}

/// `f >>> g`: arrow composition. Output of `f` feeds into `g`.
pub fn seq(
    f: Rc<dyn Fn(Value) -> Comp + 'static>,
    g: Rc<dyn Fn(Value) -> Comp + 'static>,
) -> Rc<dyn Fn(Value) -> Comp + 'static> {
    Rc::new(move |x| bind(f(x), Rc::clone(&g)))
}

/// `throw msg` — raise an exception; the continuation is never invoked.
pub fn throw(msg: &str) -> Comp {
    Comp::Op(
        Op::Throw,
        Value::Str(msg.to_string()),
        Rc::new(|_| Comp::Pure(Value::Unit)),
    )
}

/// Exception handler: `Right v` on success, `Left msg` on throw. Foreign
/// operations pass through with the handler re-applied (pass-through).
pub fn handle_exception(comp: Comp) -> Comp {
    match comp {
        Comp::Pure(v) => Comp::Pure(Value::Right(Box::new(v))),
        Comp::Op(Op::Throw, Value::Str(msg), _k) => {
            Comp::Pure(Value::Left(Box::new(Value::Str(msg))))
        }
        Comp::Op(op, arg, k) => {
            Comp::Op(op, arg, Rc::new(move |r| handle_exception(k(r))))
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum RunError {
    UnhandledOp(Op),
}

impl fmt::Display for RunError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RunError::UnhandledOp(op) => write!(f, "unhandled operation: {}", op),
        }
    }
}

pub fn run(comp: Comp) -> Result<Value, RunError> {
    match comp {
        Comp::Pure(v) => Ok(v),
        Comp::Op(op, _, _) => Err(RunError::UnhandledOp(op)),
    }
}

// ============================================================================
// The Language Protocol (Challenge #7)
// ============================================================================
//
// A language is a record of arrows. Because every operation is an arrow
// `Value ~> Comp`, they compose with `>>>` (`seq`), and a generic tool can be
// assembled as an arrow pipeline parameterized only by the Language.
//
//   parse     : Text  ~> AST          -- source text -> abstract syntax tree
//   eval      : (AST, Env) ~> Value   -- evaluate an AST in an environment
//   format    : AST   ~> Text         -- pretty-print an AST back to text
//   typecheck : AST   ~> Type         -- check an AST, yielding its type
//   lit       : Value ~> AST          -- embed a primitive value as a literal
//                                       AST node (inverse of eval on literals;
//                                       used by the generic optimizer)
//
// ASTs are represented as tagged `Value`s:
//   Product(Str tag, List [arg1, arg2, ...])
// e.g.  Product(Str "Add", [Product(Str "Int", [Int 2]), Product(Str "Int", [Int 3])])

pub struct Language {
    pub name: &'static str,
    pub parse: Rc<dyn Fn(Value) -> Comp + 'static>,
    pub eval: Rc<dyn Fn(Value) -> Comp + 'static>,
    pub format: Rc<dyn Fn(Value) -> Comp + 'static>,
    pub typecheck: Rc<dyn Fn(Value) -> Comp + 'static>,
    pub lit: Rc<dyn Fn(Value) -> Comp + 'static>,
}

// --- AST helpers -----------------------------------------------------------

/// Build a tagged AST node: `Product(Str tag, List args)`.
fn node(tag: &str, args: Vec<Value>) -> Value {
    Value::Product(
        Box::new(Value::Str(tag.to_string())),
        Box::new(Value::List(args)),
    )
}

fn ast_tag(v: &Value) -> Option<&str> {
    if let Value::Product(tag, _) = v {
        tag.as_str()
    } else {
        None
    }
}

fn ast_args(v: &Value) -> Option<&[Value]> {
    if let Value::Product(_, args) = v {
        if let Value::List(vs) = &**args {
            return Some(vs);
        }
    }
    None
}

/// Build an environment as a list of (name, value) products.
fn env_of(pairs: &[(&str, Value)]) -> Value {
    Value::List(
        pairs
            .iter()
            .map(|(n, v)| {
                Value::Product(
                    Box::new(Value::Str(n.to_string())),
                    Box::new(v.clone()),
                )
            })
            .collect(),
    )
}

fn env_empty() -> Value {
    Value::List(Vec::new())
}

/// Look up a variable in an environment.
fn lookup(env: &Value, name: &str) -> Option<Value> {
    if let Value::List(pairs) = env {
        for p in pairs {
            if let Value::Product(n, v) = p {
                if n.as_str() == Some(name) {
                    return Some((**v).clone());
                }
            }
        }
    }
    None
}

// ============================================================================
// Shared s-expression tokenizer / parser
// ============================================================================
//
// Both language instances parse an s-expression surface syntax:
//   (+ 1 (* 2 x))   (and true (not p))
// A shared tokenizer + sexpr builder produces a generic nested Value; each
// language then maps the head symbol to its own AST tag.

fn tokenize(s: &str) -> Result<Vec<String>, String> {
    let mut tokens = Vec::new();
    let mut chars = s.chars().peekable();
    while let Some(&c) = chars.peek() {
        if c.is_whitespace() {
            chars.next();
        } else if c == '(' || c == ')' {
            tokens.push(c.to_string());
            chars.next();
        } else {
            let mut atom = String::new();
            while let Some(&c) = chars.peek() {
                if c.is_whitespace() || c == '(' || c == ')' {
                    break;
                }
                atom.push(c);
                chars.next();
            }
            if atom.is_empty() {
                return Err("empty atom".to_string());
            }
            tokens.push(atom);
        }
    }
    Ok(tokens)
}

fn sexpr_from_tokens(tokens: &[String], idx: &mut usize) -> Result<Value, String> {
    if *idx >= tokens.len() {
        return Err("unexpected end of input".to_string());
    }
    let t = &tokens[*idx];
    *idx += 1;
    if t == "(" {
        let mut items = Vec::new();
        while *idx < tokens.len() && tokens[*idx] != ")" {
            items.push(sexpr_from_tokens(tokens, idx)?);
        }
        if *idx >= tokens.len() {
            return Err("missing close paren".to_string());
        }
        *idx += 1; // consume ")"
        Ok(Value::List(items))
    } else if t == ")" {
        Err("unexpected close paren".to_string())
    } else if let Ok(n) = t.parse::<i32>() {
        Ok(Value::Int(n))
    } else if t == "true" {
        Ok(Value::Bool(true))
    } else if t == "false" {
        Ok(Value::Bool(false))
    } else {
        Ok(Value::Str(t.clone()))
    }
}

fn parse_sexpr(text: &str) -> Result<Value, String> {
    let tokens = tokenize(text)?;
    if tokens.is_empty() {
        return Err("empty input".to_string());
    }
    let mut idx = 0;
    let v = sexpr_from_tokens(&tokens, &mut idx)?;
    if idx != tokens.len() {
        return Err("trailing tokens".to_string());
    }
    Ok(v)
}

// ============================================================================
// Language Instance 1: Arithmetic
// ============================================================================
//
//   AST ::= Int n | Var x | Add a b | Mul a b
//   Surface: (+ 1 (* 2 x))   |   42   |   x
//   Types:  Int (every well-formed expression has type Int)

fn arith_to_ast(v: &Value) -> Value {
    match v {
        Value::Int(n) => node("Int", vec![Value::Int(*n)]),
        Value::Str(s) => node("Var", vec![Value::Str(s.clone())]),
        Value::List(items) => {
            let head = items[0].as_str().unwrap_or("");
            match head {
                "+" => node(
                    "Add",
                    vec![arith_to_ast(&items[1]), arith_to_ast(&items[2])],
                ),
                "*" => node(
                    "Mul",
                    vec![arith_to_ast(&items[1]), arith_to_ast(&items[2])],
                ),
                _ => node("Var", vec![Value::Str(head.to_string())]),
            }
        }
        _ => Value::Unit,
    }
}

fn arith_parse(input: Value) -> Comp {
    let s = match input.as_str() {
        Some(s) => s,
        None => return throw("parse: expected text"),
    };
    match parse_sexpr(s) {
        Ok(sexpr) => pure(arith_to_ast(&sexpr)),
        Err(e) => throw(&format!("parse error: {}", e)),
    }
}

fn arith_eval(ast: Value, env: Value) -> Comp {
    match ast_tag(&ast) {
        Some("Int") => {
            let n = ast_args(&ast).unwrap()[0].clone();
            pure(n)
        }
        Some("Var") => {
            let name = ast_args(&ast).unwrap()[0].clone();
            match lookup(&env, name.as_str().unwrap_or("")) {
                Some(v) => pure(v),
                None => throw("unbound variable"),
            }
        }
        Some("Add") => {
            let args = ast_args(&ast).unwrap();
            let l = arith_eval(args[0].clone(), env.clone());
            let r_arg = args[1].clone();
            let env2 = env.clone();
            bind(l, Rc::new(move |lv| {
                let ln = lv.as_int().unwrap_or(0);
                let r = arith_eval(r_arg.clone(), env2.clone());
                bind(r, Rc::new(move |rv| {
                    let rn = rv.as_int().unwrap_or(0);
                    pure(Value::Int(ln + rn))
                }))
            }))
        }
        Some("Mul") => {
            let args = ast_args(&ast).unwrap();
            let l = arith_eval(args[0].clone(), env.clone());
            let r_arg = args[1].clone();
            let env2 = env.clone();
            bind(l, Rc::new(move |lv| {
                let ln = lv.as_int().unwrap_or(0);
                let r = arith_eval(r_arg.clone(), env2.clone());
                bind(r, Rc::new(move |rv| {
                    let rn = rv.as_int().unwrap_or(0);
                    pure(Value::Int(ln * rn))
                }))
            }))
        }
        _ => throw("eval: unknown node"),
    }
}

fn arith_eval_arrow(input: Value) -> Comp {
    if let Value::Product(ast, env) = input {
        arith_eval((*ast).clone(), (*env).clone())
    } else {
        throw("eval expects (AST, Env)")
    }
}

fn arith_typecheck(ast: Value) -> Comp {
    let tag = ast_tag(&ast).unwrap_or("").to_string();
    match tag.as_str() {
        "Int" | "Var" => pure(Value::Str("Int".to_string())),
        "Bool" => throw("type error: expected Int, got Bool"),
        "Add" | "Mul" => {
            let args = ast_args(&ast).unwrap();
            let lt = arith_typecheck(args[0].clone());
            let r_arg = args[1].clone();
            bind(lt, Rc::new(move |lv| {
                if lv == Value::Str("Int".to_string()) {
                    let rt = arith_typecheck(r_arg.clone());
                    bind(rt, Rc::new(move |rv| {
                        if rv == Value::Str("Int".to_string()) {
                            pure(Value::Str("Int".to_string()))
                        } else {
                            throw("type error: expected Int operand")
                        }
                    }))
                } else {
                    throw("type error: expected Int operand")
                }
            }))
        }
        _ => throw("type error: unknown node"),
    }
}

fn arith_format(ast: Value) -> Comp {
    let tag = ast_tag(&ast).unwrap_or("").to_string();
    match tag.as_str() {
        "Int" => {
            let n = ast_args(&ast).unwrap()[0].as_int().unwrap_or(0);
            pure(Value::Str(n.to_string()))
        }
        "Var" => {
            let s = ast_args(&ast).unwrap()[0].as_str().unwrap_or("").to_string();
            pure(Value::Str(s))
        }
        "Add" | "Mul" => {
            let op = if tag == "Add" { "+" } else { "*" };
            let args = ast_args(&ast).unwrap();
            let lf = arith_format(args[0].clone());
            let r_arg = args[1].clone();
            let op_s = op.to_string();
            bind(lf, Rc::new(move |ls| {
                let rs = arith_format(r_arg.clone());
                let op2 = op_s.clone();
                bind(rs, Rc::new(move |rsv| {
                    let s = format!(
                        "({} {} {})",
                        op2,
                        ls.as_str().unwrap_or(""),
                        rsv.as_str().unwrap_or("")
                    );
                    pure(Value::Str(s))
                }))
            }))
        }
        _ => throw("format: unknown node"),
    }
}

fn arith_lit(v: Value) -> Comp {
    match v {
        Value::Int(n) => pure(node("Int", vec![Value::Int(n)])),
        _ => throw("lit: not an Int value"),
    }
}

pub fn arith_language() -> Language {
    Language {
        name: "Arithmetic",
        parse: Rc::new(arith_parse),
        eval: Rc::new(arith_eval_arrow),
        format: Rc::new(arith_format),
        typecheck: Rc::new(arith_typecheck),
        lit: Rc::new(arith_lit),
    }
}

// ============================================================================
// Language Instance 2: Boolean / Logic
// ============================================================================
//
//   AST ::= Bool b | Var x | And a b | Or a b | Not a
//   Surface: (and true (not p))   |   true   |   p
//   Types:  Bool

fn bool_to_ast(v: &Value) -> Value {
    match v {
        Value::Bool(b) => node("Bool", vec![Value::Bool(*b)]),
        Value::Str(s) => node("Var", vec![Value::Str(s.clone())]),
        Value::List(items) => {
            let head = items[0].as_str().unwrap_or("");
            match head {
                "and" => node(
                    "And",
                    vec![bool_to_ast(&items[1]), bool_to_ast(&items[2])],
                ),
                "or" => node(
                    "Or",
                    vec![bool_to_ast(&items[1]), bool_to_ast(&items[2])],
                ),
                "not" => node("Not", vec![bool_to_ast(&items[1])]),
                _ => node("Var", vec![Value::Str(head.to_string())]),
            }
        }
        _ => Value::Unit,
    }
}

fn bool_parse(input: Value) -> Comp {
    let s = match input.as_str() {
        Some(s) => s,
        None => return throw("parse: expected text"),
    };
    match parse_sexpr(s) {
        Ok(sexpr) => pure(bool_to_ast(&sexpr)),
        Err(e) => throw(&format!("parse error: {}", e)),
    }
}

fn bool_eval(ast: Value, env: Value) -> Comp {
    match ast_tag(&ast) {
        Some("Bool") => {
            let b = ast_args(&ast).unwrap()[0].as_bool().unwrap_or(false);
            pure(Value::Bool(b))
        }
        Some("Var") => {
            let name = ast_args(&ast).unwrap()[0].clone();
            match lookup(&env, name.as_str().unwrap_or("")) {
                Some(v) => pure(v),
                None => throw("unbound variable"),
            }
        }
        Some("And") => {
            let args = ast_args(&ast).unwrap();
            let l = bool_eval(args[0].clone(), env.clone());
            let r_arg = args[1].clone();
            let env2 = env.clone();
            bind(l, Rc::new(move |lv| {
                let lb = lv.as_bool().unwrap_or(false);
                let r = bool_eval(r_arg.clone(), env2.clone());
                bind(r, Rc::new(move |rv| {
                    let rb = rv.as_bool().unwrap_or(false);
                    pure(Value::Bool(lb && rb))
                }))
            }))
        }
        Some("Or") => {
            let args = ast_args(&ast).unwrap();
            let l = bool_eval(args[0].clone(), env.clone());
            let r_arg = args[1].clone();
            let env2 = env.clone();
            bind(l, Rc::new(move |lv| {
                let lb = lv.as_bool().unwrap_or(false);
                let r = bool_eval(r_arg.clone(), env2.clone());
                bind(r, Rc::new(move |rv| {
                    let rb = rv.as_bool().unwrap_or(false);
                    pure(Value::Bool(lb || rb))
                }))
            }))
        }
        Some("Not") => {
            let args = ast_args(&ast).unwrap();
            let a = bool_eval(args[0].clone(), env);
            bind(a, Rc::new(move |av| {
                let b = av.as_bool().unwrap_or(false);
                pure(Value::Bool(!b))
            }))
        }
        _ => throw("eval: unknown node"),
    }
}

fn bool_eval_arrow(input: Value) -> Comp {
    if let Value::Product(ast, env) = input {
        bool_eval((*ast).clone(), (*env).clone())
    } else {
        throw("eval expects (AST, Env)")
    }
}

fn bool_typecheck(ast: Value) -> Comp {
    let tag = ast_tag(&ast).unwrap_or("").to_string();
    match tag.as_str() {
        "Bool" | "Var" => pure(Value::Str("Bool".to_string())),
        "Int" => throw("type error: expected Bool, got Int"),
        "And" | "Or" => {
            let args = ast_args(&ast).unwrap();
            let lt = bool_typecheck(args[0].clone());
            let r_arg = args[1].clone();
            bind(lt, Rc::new(move |lv| {
                if lv == Value::Str("Bool".to_string()) {
                    let rt = bool_typecheck(r_arg.clone());
                    bind(rt, Rc::new(move |rv| {
                        if rv == Value::Str("Bool".to_string()) {
                            pure(Value::Str("Bool".to_string()))
                        } else {
                            throw("type error: expected Bool operand")
                        }
                    }))
                } else {
                    throw("type error: expected Bool operand")
                }
            }))
        }
        "Not" => {
            let args = ast_args(&ast).unwrap();
            let ct = bool_typecheck(args[0].clone());
            bind(ct, Rc::new(move |cv| {
                if cv == Value::Str("Bool".to_string()) {
                    pure(Value::Str("Bool".to_string()))
                } else {
                    throw("type error: expected Bool operand")
                }
            }))
        }
        _ => throw("type error: unknown node"),
    }
}

fn bool_format(ast: Value) -> Comp {
    let tag = ast_tag(&ast).unwrap_or("").to_string();
    match tag.as_str() {
        "Bool" => {
            let b = ast_args(&ast).unwrap()[0].as_bool().unwrap_or(false);
            pure(Value::Str(b.to_string()))
        }
        "Var" => {
            let s = ast_args(&ast).unwrap()[0].as_str().unwrap_or("").to_string();
            pure(Value::Str(s))
        }
        "And" | "Or" => {
            let op = if tag == "And" { "and" } else { "or" };
            let args = ast_args(&ast).unwrap();
            let lf = bool_format(args[0].clone());
            let r_arg = args[1].clone();
            let op_s = op.to_string();
            bind(lf, Rc::new(move |ls| {
                let rs = bool_format(r_arg.clone());
                let op2 = op_s.clone();
                bind(rs, Rc::new(move |rsv| {
                    let s = format!(
                        "({} {} {})",
                        op2,
                        ls.as_str().unwrap_or(""),
                        rsv.as_str().unwrap_or("")
                    );
                    pure(Value::Str(s))
                }))
            }))
        }
        "Not" => {
            let args = ast_args(&ast).unwrap();
            let af = bool_format(args[0].clone());
            bind(af, Rc::new(move |asv| {
                let s = format!("(not {})", asv.as_str().unwrap_or(""));
                pure(Value::Str(s))
            }))
        }
        _ => throw("format: unknown node"),
    }
}

fn bool_lit(v: Value) -> Comp {
    match v {
        Value::Bool(b) => pure(node("Bool", vec![Value::Bool(b)])),
        _ => throw("lit: not a Bool value"),
    }
}

pub fn bool_language() -> Language {
    Language {
        name: "Boolean",
        parse: Rc::new(bool_parse),
        eval: Rc::new(bool_eval_arrow),
        format: Rc::new(bool_format),
        typecheck: Rc::new(bool_typecheck),
        lit: Rc::new(bool_lit),
    }
}

// ============================================================================
// Generic Language-Agnostic Tools (Challenge #8)
// ============================================================================
//
// Each tool is a function `&Language -> ...`. It builds arrow pipelines from
// the language's own arrows. The SAME tool code runs against every language
// instance — only the Language parameter differs.

/// Run a computation under the exception handler, returning `Ok v` on success
/// or `Err msg` on a caught throw. This is the universal "try" used by tools.
fn run_handled(comp: Comp) -> Result<Value, String> {
    match run(handle_exception(comp)) {
        Ok(Value::Right(v)) => Ok(*v),
        Ok(Value::Left(e)) => match *e {
            Value::Str(s) => Err(s),
            other => Err(format!("error: {}", other)),
        },
        Ok(other) => Err(format!("unexpected: {}", other)),
        Err(e) => Err(format!("{}", e)),
    }
}

/// Generic pretty-printer: `Language -> AST -> Text`.
/// Uses only the language's `format` arrow. Works on any language.
fn pretty_print(lang: &Language, ast: &Value) -> String {
    match run_handled((lang.format)(ast.clone())) {
        Ok(v) => v.as_str().unwrap_or("?").to_string(),
        Err(e) => format!("<format error: {}>", e),
    }
}

/// Generic error reporter: `Language -> AST -> Env -> String`.
/// Runs `typecheck` then `eval` under the exception handler, formatting a
/// human-readable message. Catches both type and runtime errors. Works on any
/// language.
fn report_error(lang: &Language, ast: &Value, env: &Value) -> String {
    let ty = match run_handled((lang.typecheck)(ast.clone())) {
        Ok(t) => t.as_str().unwrap_or("?").to_string(),
        Err(e) => return format!("[{}] Type error: {}", lang.name, e),
    };
    let input = Value::Product(Box::new(ast.clone()), Box::new(env.clone()));
    match run_handled((lang.eval)(input)) {
        Ok(v) => format!("[{}] OK ({}): {}", lang.name, ty, v),
        Err(e) => format!("[{}] Runtime error: {}", lang.name, e),
    }
}

/// Generic optimizer (constant folding): `Language -> AST -> AST`.
/// Recursively optimizes children, then attempts to `eval` the node with an
/// empty environment. If evaluation succeeds (no unbound variables / errors),
/// the node is replaced by its literal value (via the language's `lit` arrow).
/// Otherwise the node is kept with its optimized children. Uses only the
/// language's `eval` and `lit` arrows plus the generic AST structure — works
/// on any language.
fn optimize(lang: &Language, ast: &Value) -> Value {
    if let Value::Product(tag, args_box) = ast {
        if let Value::List(args) = &**args_box {
            let new_args: Vec<Value> = args.iter().map(|a| optimize(lang, a)).collect();
            let new_node = Value::Product(
                Box::new((**tag).clone()),
                Box::new(Value::List(new_args)),
            );
            // eval the node with an empty environment, via an arrow pipeline:
            //   arr (pair with empty env)  >>>  lang.eval
            let eval_with_empty: Rc<dyn Fn(Value) -> Comp + 'static> = seq(
                arr(|a| Value::Product(Box::new(a), Box::new(Value::List(Vec::new())))),
                Rc::clone(&lang.eval),
            );
            return match run_handled(eval_with_empty(new_node.clone())) {
                Ok(v) => match run_handled((lang.lit)(v)) {
                    Ok(lit_ast) => lit_ast,
                    Err(_) => new_node,
                },
                Err(_) => new_node,
            };
        }
    }
    ast.clone()
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // --- Language instance 1: Arithmetic -----------------------------------

    #[test]
    fn test_arith_parse_add() {
        let lang = arith_language();
        let ast = run((lang.parse)(Value::Str("(+ 1 2)".to_string()))).unwrap();
        assert_eq!(
            ast,
            node(
                "Add",
                vec![
                    node("Int", vec![Value::Int(1)]),
                    node("Int", vec![Value::Int(2)])
                ]
            )
        );
    }

    #[test]
    fn test_arith_eval_add() {
        let lang = arith_language();
        let ast = node(
            "Add",
            vec![
                node("Int", vec![Value::Int(2)]),
                node("Int", vec![Value::Int(3)]),
            ],
        );
        let input = Value::Product(Box::new(ast), Box::new(env_empty()));
        assert_eq!(run((lang.eval)(input)).unwrap(), Value::Int(5));
    }

    #[test]
    fn test_arith_eval_var() {
        let lang = arith_language();
        let ast = node(
            "Add",
            vec![
                node("Var", vec![Value::Str("x".to_string())]),
                node("Int", vec![Value::Int(3)]),
            ],
        );
        let env = env_of(&[("x", Value::Int(7))]);
        let input = Value::Product(Box::new(ast), Box::new(env));
        assert_eq!(run((lang.eval)(input)).unwrap(), Value::Int(10));
    }

    #[test]
    fn test_arith_format_add() {
        let lang = arith_language();
        let ast = node(
            "Add",
            vec![
                node("Int", vec![Value::Int(1)]),
                node(
                    "Mul",
                    vec![
                        node("Int", vec![Value::Int(2)]),
                        node("Var", vec![Value::Str("x".to_string())]),
                    ],
                ),
            ],
        );
        let out = run((lang.format)(ast)).unwrap();
        assert_eq!(out, Value::Str("(+ 1 (* 2 x))".to_string()));
    }

    #[test]
    fn test_arith_typecheck_ok() {
        let lang = arith_language();
        let ast = node(
            "Add",
            vec![
                node("Int", vec![Value::Int(1)]),
                node("Var", vec![Value::Str("x".to_string())]),
            ],
        );
        assert_eq!(
            run((lang.typecheck)(ast)).unwrap(),
            Value::Str("Int".to_string())
        );
    }

    #[test]
    fn test_arith_typecheck_error() {
        let lang = arith_language();
        let ast = node(
            "Add",
            vec![
                node("Bool", vec![Value::Bool(true)]),
                node("Int", vec![Value::Int(1)]),
            ],
        );
        let res = run(handle_exception((lang.typecheck)(ast))).unwrap();
        assert_eq!(
            res,
            Value::Left(Box::new(Value::Str(
                "type error: expected Int, got Bool".to_string()
            )))
        );
    }

    // --- Language instance 2: Boolean --------------------------------------

    #[test]
    fn test_bool_parse_and() {
        let lang = bool_language();
        let ast = run((lang.parse)(Value::Str("(and true false)".to_string()))).unwrap();
        assert_eq!(
            ast,
            node(
                "And",
                vec![
                    node("Bool", vec![Value::Bool(true)]),
                    node("Bool", vec![Value::Bool(false)])
                ]
            )
        );
    }

    #[test]
    fn test_bool_eval_and() {
        let lang = bool_language();
        let ast = node(
            "And",
            vec![
                node("Bool", vec![Value::Bool(true)]),
                node("Bool", vec![Value::Bool(false)]),
            ],
        );
        let input = Value::Product(Box::new(ast), Box::new(env_empty()));
        assert_eq!(run((lang.eval)(input)).unwrap(), Value::Bool(false));
    }

    #[test]
    fn test_bool_eval_not() {
        let lang = bool_language();
        let ast = node("Not", vec![node("Bool", vec![Value::Bool(true)])]);
        let input = Value::Product(Box::new(ast), Box::new(env_empty()));
        assert_eq!(run((lang.eval)(input)).unwrap(), Value::Bool(false));
    }

    #[test]
    fn test_bool_format_or() {
        let lang = bool_language();
        let ast = node(
            "Or",
            vec![
                node("Var", vec![Value::Str("p".to_string())]),
                node("Not", vec![node("Bool", vec![Value::Bool(false)])]),
            ],
        );
        let out = run((lang.format)(ast)).unwrap();
        assert_eq!(out, Value::Str("(or p (not false))".to_string()));
    }

    #[test]
    fn test_bool_typecheck_ok() {
        let lang = bool_language();
        let ast = node(
            "And",
            vec![
                node("Bool", vec![Value::Bool(true)]),
                node("Var", vec![Value::Str("p".to_string())]),
            ],
        );
        assert_eq!(
            run((lang.typecheck)(ast)).unwrap(),
            Value::Str("Bool".to_string())
        );
    }

    #[test]
    fn test_bool_typecheck_error() {
        let lang = bool_language();
        let ast = node(
            "And",
            vec![
                node("Int", vec![Value::Int(1)]),
                node("Bool", vec![Value::Bool(true)]),
            ],
        );
        let res = run(handle_exception((lang.typecheck)(ast))).unwrap();
        assert_eq!(
            res,
            Value::Left(Box::new(Value::Str(
                "type error: expected Bool, got Int".to_string()
            )))
        );
    }

    // --- Generic pretty-printer (works on both languages) ------------------

    #[test]
    fn test_pretty_print_arith() {
        let lang = arith_language();
        let ast = node(
            "Add",
            vec![
                node("Int", vec![Value::Int(1)]),
                node("Int", vec![Value::Int(2)]),
            ],
        );
        assert_eq!(pretty_print(&lang, &ast), "(+ 1 2)");
    }

    #[test]
    fn test_pretty_print_bool() {
        let lang = bool_language();
        let ast = node(
            "And",
            vec![
                node("Bool", vec![Value::Bool(true)]),
                node("Bool", vec![Value::Bool(false)]),
            ],
        );
        assert_eq!(pretty_print(&lang, &ast), "(and true false)");
    }

    // --- Generic error reporter (works on both languages) ------------------

    #[test]
    fn test_report_error_arith_unbound() {
        let lang = arith_language();
        let ast = node("Var", vec![Value::Str("y".to_string())]);
        let msg = report_error(&lang, &ast, &env_empty());
        assert!(msg.contains("Runtime error") && msg.contains("unbound"));
    }

    #[test]
    fn test_report_error_arith_type_error() {
        let lang = arith_language();
        let ast = node(
            "Add",
            vec![
                node("Bool", vec![Value::Bool(true)]),
                node("Int", vec![Value::Int(1)]),
            ],
        );
        let msg = report_error(&lang, &ast, &env_empty());
        assert!(msg.contains("Type error"));
    }

    #[test]
    fn test_report_error_bool_success() {
        let lang = bool_language();
        let ast = node(
            "And",
            vec![
                node("Bool", vec![Value::Bool(true)]),
                node("Bool", vec![Value::Bool(true)]),
            ],
        );
        let msg = report_error(&lang, &ast, &env_empty());
        assert!(msg.contains("OK") && msg.contains("true"));
    }

    // --- Generic optimizer (constant folding, works on both languages) -----

    #[test]
    fn test_optimize_arith_constant_fold() {
        let lang = arith_language();
        let ast = node(
            "Add",
            vec![
                node("Int", vec![Value::Int(2)]),
                node(
                    "Mul",
                    vec![
                        node("Int", vec![Value::Int(3)]),
                        node("Int", vec![Value::Int(4)]),
                    ],
                ),
            ],
        );
        let opt = optimize(&lang, &ast);
        assert_eq!(opt, node("Int", vec![Value::Int(14)]));
    }

    #[test]
    fn test_optimize_arith_keeps_vars() {
        let lang = arith_language();
        let ast = node(
            "Add",
            vec![
                node("Var", vec![Value::Str("x".to_string())]),
                node("Int", vec![Value::Int(3)]),
            ],
        );
        let opt = optimize(&lang, &ast);
        assert_eq!(opt, ast); // unbound x -> cannot fold -> unchanged
    }

    #[test]
    fn test_optimize_bool_constant_fold() {
        let lang = bool_language();
        // (and true (not false)) = true && true = true
        let ast = node(
            "And",
            vec![
                node("Bool", vec![Value::Bool(true)]),
                node("Not", vec![node("Bool", vec![Value::Bool(false)])]),
            ],
        );
        let opt = optimize(&lang, &ast);
        assert_eq!(opt, node("Bool", vec![Value::Bool(true)]));
    }

    // --- Round-trip: parse >>> format >>> parse -----------------------------

    #[test]
    fn test_roundtrip_arith() {
        let lang = arith_language();
        let text = Value::Str("(+ 1 (* 2 x))".to_string());
        let ast1 = run((lang.parse)(text.clone())).unwrap();
        let pipeline = seq(
            Rc::clone(&lang.parse),
            seq(Rc::clone(&lang.format), Rc::clone(&lang.parse)),
        );
        let ast2 = run(pipeline(text)).unwrap();
        assert_eq!(ast1, ast2);
    }

    #[test]
    fn test_roundtrip_bool() {
        let lang = bool_language();
        let text = Value::Str("(or true (not false))".to_string());
        let ast1 = run((lang.parse)(text.clone())).unwrap();
        let pipeline = seq(
            Rc::clone(&lang.parse),
            seq(Rc::clone(&lang.format), Rc::clone(&lang.parse)),
        );
        let ast2 = run(pipeline(text)).unwrap();
        assert_eq!(ast1, ast2);
    }

    // --- Composition: parse >>> eval / parse >>> typecheck -----------------

    #[test]
    fn test_compose_parse_eval_arith() {
        let lang = arith_language();
        let env = env_empty();
        let pair: Rc<dyn Fn(Value) -> Comp + 'static> =
            Rc::new(move |ast| {
                pure(Value::Product(Box::new(ast), Box::new(env.clone())))
            });
        let pipeline = seq(Rc::clone(&lang.parse), seq(pair, Rc::clone(&lang.eval)));
        let result = run(pipeline(Value::Str("(+ 2 3)".to_string()))).unwrap();
        assert_eq!(result, Value::Int(5));
    }

    #[test]
    fn test_compose_parse_typecheck_arith() {
        let lang = arith_language();
        let pipeline = seq(Rc::clone(&lang.parse), Rc::clone(&lang.typecheck));
        let result = run(pipeline(Value::Str("(+ 1 (* 2 3))".to_string()))).unwrap();
        assert_eq!(result, Value::Str("Int".to_string()));
    }

    // --- Same tool, different languages -> language-specific results -------

    #[test]
    fn test_same_tool_different_languages_pretty_print() {
        let arith = arith_language();
        let bool = bool_language();
        let a_ast = run((arith.parse)(Value::Str("(+ 1 2)".to_string()))).unwrap();
        let b_ast = run((bool.parse)(Value::Str("(and true false)".to_string()))).unwrap();
        // The SAME pretty_print function, parameterized only by the language.
        let a_out = pretty_print(&arith, &a_ast);
        let b_out = pretty_print(&bool, &b_ast);
        assert_eq!(a_out, "(+ 1 2)");
        assert_eq!(b_out, "(and true false)");
        assert_ne!(a_out, b_out);
    }

    #[test]
    fn test_same_tool_different_languages_optimize() {
        let arith = arith_language();
        let bool = bool_language();
        let a_ast = node(
            "Add",
            vec![
                node("Int", vec![Value::Int(4)]),
                node("Int", vec![Value::Int(5)]),
            ],
        );
        let b_ast = node(
            "Or",
            vec![
                node("Bool", vec![Value::Bool(false)]),
                node("Bool", vec![Value::Bool(true)]),
            ],
        );
        // The SAME optimize function folds each to its language's literal.
        let a_opt = optimize(&arith, &a_ast);
        let b_opt = optimize(&bool, &b_ast);
        assert_eq!(a_opt, node("Int", vec![Value::Int(9)]));
        assert_eq!(b_opt, node("Bool", vec![Value::Bool(true)]));
    }

    // --- lit necessity: is lit needed for tooling or only optimization? -----

    /// A language with a broken `lit` (always throws). Used to test whether
    /// `lit` is necessary for each generic tool.
    fn arith_broken_lit() -> Language {
        let base = arith_language();
        Language {
            name: "Arith (broken lit)",
            parse: base.parse,
            eval: base.eval,
            format: base.format,
            typecheck: base.typecheck,
            lit: Rc::new(|_| throw("lit: broken")),
        }
    }

    #[test]
    fn test_lit_not_needed_for_pretty_print() {
        let lang = arith_broken_lit();
        let ast = node(
            "Add",
            vec![
                node("Int", vec![Value::Int(1)]),
                node("Int", vec![Value::Int(2)]),
            ],
        );
        // pretty_print uses only format — lit is never called.
        let out = pretty_print(&lang, &ast);
        assert_eq!(out, "(+ 1 2)");
    }

    #[test]
    fn test_lit_not_needed_for_error_report() {
        let lang = arith_broken_lit();
        let ast = node(
            "Add",
            vec![
                node("Int", vec![Value::Int(1)]),
                node("Bool", vec![Value::Bool(true)]),
            ],
        );
        // report_error uses only typecheck + eval — lit is never called.
        let env = env_empty();
        let msg = report_error(&lang, &ast, &env);
        assert!(msg.contains("Type error") || msg.contains("Runtime error"));
    }

    #[test]
    fn test_lit_not_needed_for_parse_eval_pipeline() {
        let lang = arith_broken_lit();
        // parse >>> eval pipeline works without lit.
        let env = env_empty();
        let pair: Rc<dyn Fn(Value) -> Comp + 'static> =
            Rc::new(move |ast| {
                pure(Value::Product(Box::new(ast), Box::new(env.clone())))
            });
        let pipeline = seq(Rc::clone(&lang.parse), seq(pair, Rc::clone(&lang.eval)));
        let result = run(pipeline(Value::Str("(+ 2 3)".to_string()))).unwrap();
        assert_eq!(result, Value::Int(5));
    }

    #[test]
    fn test_lit_needed_for_optimize() {
        let lang = arith_broken_lit();
        let ast = node(
            "Add",
            vec![
                node("Int", vec![Value::Int(2)]),
                node("Int", vec![Value::Int(3)]),
            ],
        );
        // optimize calls lit to re-embed the folded value. With broken lit,
        // it falls back to the un-folded node (eval succeeds but lit fails).
        let opt = optimize(&lang, &ast);
        // The node is kept as-is because lit failed — not folded to Int(5).
        assert_eq!(opt, ast);
    }

    #[test]
    fn test_lit_is_inverse_of_eval_on_literals() {
        let lang = arith_language();
        // lit(eval(Int(n))) = Int(n) — lit inverts eval on literals.
        let n = Value::Int(42);
        let lit_ast = run((lang.lit)(n.clone())).unwrap();
        assert_eq!(lit_ast, node("Int", vec![Value::Int(42)]));
        // And eval(lit(n)) = n — roundtrip.
        let input = Value::Product(Box::new(lit_ast), Box::new(env_empty()));
        assert_eq!(run((lang.eval)(input)).unwrap(), Value::Int(42));
    }
}

// ============================================================================
// Demo
// ============================================================================

fn main() {
    println!("Arrow Calculus: Challenges #7 & #8 - Language Protocol & Generic Tooling");
    println!("===========================================================================\n");

    let arith = arith_language();
    let bool = bool_language();

    // Demo 1: parse + eval on each language
    println!("Demo 1: parse >>> eval (Arithmetic)");
    let env = env_of(&[("x", Value::Int(10))]);
    let pair: Rc<dyn Fn(Value) -> Comp + 'static> = {
        let env = env.clone();
        Rc::new(move |ast| pure(Value::Product(Box::new(ast), Box::new(env.clone()))))
    };
    let pipeline = seq(Rc::clone(&arith.parse), seq(pair, Rc::clone(&arith.eval)));
    match run(pipeline(Value::Str("(+ 2 (* 3 x))".to_string()))) {
        Ok(v) => println!("  (+ 2 (* 3 x)) with x=10  ->  {} (expected 32)\n", v),
        Err(e) => println!("  error: {}\n", e),
    }

    println!("Demo 2: parse >>> eval (Boolean)");
    match run((bool.eval)(Value::Product(
        Box::new(run((bool.parse)(Value::Str("(or false (not false))".to_string()))).unwrap()),
        Box::new(env_empty()),
    ))) {
        Ok(v) => println!("  (or false (not false))  ->  {} (expected true)\n", v),
        Err(e) => println!("  error: {}\n", e),
    }

    // Demo 3: generic pretty-printer on both languages
    println!("Demo 3: generic pretty_print (same code, two languages)");
    let a_ast = run((arith.parse)(Value::Str("(+ 1 (* 2 3))".to_string()))).unwrap();
    let b_ast = run((bool.parse)(Value::Str("(and true (not p))".to_string()))).unwrap();
    println!("  arith: {}", pretty_print(&arith, &a_ast));
    println!("  bool : {}\n", pretty_print(&bool, &b_ast));

    // Demo 4: generic error reporter
    println!("Demo 4: generic report_error");
    let bad_ast = node("Var", vec![Value::Str("missing".to_string())]);
    println!("  arith unbound: {}", report_error(&arith, &bad_ast, &env_empty()));
    let type_err = node(
        "Add",
        vec![node("Bool", vec![Value::Bool(true)]),
             node("Int", vec![Value::Int(1)])],
    );
    println!("  arith type err: {}\n", report_error(&arith, &type_err, &env_empty()));

    // Demo 5: generic optimizer (constant folding) on both languages
    println!("Demo 5: generic optimize (constant folding)");
    let a_fold = node(
        "Add",
        vec![
            node("Int", vec![Value::Int(2)]),
            node("Mul", vec![node("Int", vec![Value::Int(3)]),
                            node("Int", vec![Value::Int(4)])]),
        ],
    );
    println!("  arith: {} -> {}", pretty_print(&arith, &a_fold), pretty_print(&arith, &optimize(&arith, &a_fold)));
    let b_fold = node(
        "And",
        vec![node("Bool", vec![Value::Bool(true)]),
             node("Not", vec![node("Bool", vec![Value::Bool(false)])])],
    );
    println!("  bool : {} -> {}\n", pretty_print(&bool, &b_fold), pretty_print(&bool, &optimize(&bool, &b_fold)));

    // Demo 6: round-trip parse >>> format >>> parse
    println!("Demo 6: round-trip parse >>> format >>> parse (Arithmetic)");
    let text = Value::Str("(+ 1 (* 2 x))".to_string());
    let rt = seq(
        Rc::clone(&arith.parse),
        seq(Rc::clone(&arith.format), Rc::clone(&arith.parse)),
    );
    let ast = run(rt(text)).unwrap();
    println!("  result AST: {}\n", ast);

    println!("Key result: the SAME pretty_print / report_error / optimize code");
    println!("runs unchanged over both language instances — only the Language");
    println!("parameter differs. Tools are arrow pipelines assembled from each");
    println!("language's own parse/eval/format/typecheck/lit arrows.");
}
