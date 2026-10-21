// handl v0.1 Surface Syntax — Reference Parser and Pretty-Printer
// ADR-0074 follow-up #6.
//
// This is a reference implementation of the v0.1 surface syntax defined in
// ARROW_LANGUAGE_SPEC_V0_1.md, parsed per ARROW_GRAMMAR_V0_1.md, and desugared
// to the kernel IR (ADR-0052) per ARROW_DESUGARING_V0_1.md.
//
// It is std-only (no external dependencies). It is deliberately a *reference*
// implementation: it prioritizes clarity and round-trip fidelity over
// performance. See the "Limitations" note at the end of this file.
//
// Style note: this PoC uses standalone test binaries with `fn main()` (see
// `src/recursion_tests.rs`). This file is both a library-of-sorts (the modules
// are pub) and a binary with a smoke-test `main()`.

// ============================================================================
// Module: lexer
// ============================================================================

pub mod lexer {
    #[derive(Debug, Clone, PartialEq)]
    pub enum Token {
        // Literals
        Int(i64),
        Float(f64),
        Str(String),
        Ident(String),
        Wild, // `_`
        // Keywords
        KwIf,
        KwElse,
        KwMatch,
        KwRec,
        KwWhile,
        KwDo,
        KwFor,
        KwIn,
        KwReturn,
        KwImport,
        KwExport,
        KwFrom,
        KwAs,
        KwInfer,
        KwType,
        KwTrue,
        KwFalse,
        KwHandle, // handle ... with (ADR-0076 handler-based trait resolution)
        KwWith,
        KwLaw,    // law <name>: <equation>  (ADR-0076 law declaration)
        KwForall, // forall <vars>. <expr>   (universal quantifier for laws)
        // Operators / punctuation
        Arrow,       // ~>
        Seq,         // >>>
        Product,     // ***
        FanOut,      // &&&
        Choice,      // |||
        Nullish,     // ??
        OptChain,    // ?.
        Assign,      // =
        Colon,       // :
        Comma,       // ,
        Semicolon,   // ;
        Dot,          // .
        LBrack,      // [
        RBrack,      // ]
        LBrace,      // {
        RBrace,      // }
        LParen,      // (
        RParen,      // )
        Ellipsis,    // ...
        Pipe,        // |
        // End
        Eof,
    }

    impl Token {
        /// The left-binding-power for an infix operator token, or None if the
        /// token is not an infix operator. From ARROW_GRAMMAR_V0_1.md §3.2.
        pub fn lbp(&self) -> Option<u8> {
            match self {
                Token::Dot | Token::LBrack => Some(90), // postfix field/index
                Token::OptChain => Some(60),            // postfix ?.
                Token::Nullish => Some(60),             // infix ??
                Token::Product | Token::FanOut => Some(50),
                Token::Seq => Some(40),
                Token::Choice => Some(30),
                Token::Arrow => Some(20), // right-assoc
                // Arithmetic (library operators), level 6.
                // We encode them as Ident in the lexer and resolve in the
                // parser, so they don't appear here.
                _ => None,
            }
        }
    }

    #[derive(Clone)]
    pub struct Lexer<'a> {
        src: &'a [u8],
        pos: usize,
        pub line: usize,
        pub col: usize,
    }

    #[derive(Debug, Clone, PartialEq)]
    pub struct LexError {
        pub msg: String,
        pub line: usize,
        pub col: usize,
    }

    impl std::fmt::Display for LexError {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "lex error at {}:{}: {}", self.line, self.col, self.msg)
        }
    }

    fn is_ident_start(c: u8) -> bool {
        c.is_ascii_alphabetic() || c == b'_'
    }
    fn is_ident_cont(c: u8) -> bool {
        c.is_ascii_alphanumeric() || c == b'_'
    }

    impl<'a> Lexer<'a> {
        pub fn new(src: &'a str) -> Self {
            Lexer { src: src.as_bytes(), pos: 0, line: 1, col: 1 }
        }

        fn peek(&self) -> Option<u8> {
            self.src.get(self.pos).copied()
        }
        fn peek2(&self) -> Option<u8> {
            self.src.get(self.pos + 1).copied()
        }
        fn peek3(&self) -> Option<u8> {
            self.src.get(self.pos + 2).copied()
        }
        fn advance(&mut self) -> Option<u8> {
            let c = self.peek()?;
            self.pos += 1;
            if c == b'\n' {
                self.line += 1;
                self.col = 1;
            } else {
                self.col += 1;
            }
            Some(c)
        }

        fn skip_ws_and_comments(&mut self) {
            loop {
                match self.peek() {
                    Some(c) if c.is_ascii_whitespace() => {
                        self.advance();
                    }
                    Some(b'-') if self.peek2() == Some(b'-') => {
                        // line comment
                        while let Some(c) = self.peek() {
                            if c == b'\n' {
                                break;
                            }
                            self.advance();
                        }
                    }
                    _ => break,
                }
            }
        }

        pub fn next_token(&mut self) -> Result<Token, LexError> {
            self.skip_ws_and_comments();
            let c = match self.peek() {
                Some(c) => c,
                None => return Ok(Token::Eof),
            };
            let start_line = self.line;
            let start_col = self.col;

            // Numbers
            if c.is_ascii_digit() {
                return self.lex_number(start_line, start_col);
            }
            // Identifiers / keywords / `_`
            if is_ident_start(c) {
                return self.lex_ident(start_line, start_col);
            }
            // Strings
            if c == b'"' {
                return self.lex_string(start_line, start_col);
            }

            // Operators / punctuation
            self.advance();
            let tok = match c {
                b'~' => {
                    if self.peek() == Some(b'>') {
                        self.advance();
                        Token::Arrow
                    } else {
                        return Err(self.err(start_line, start_col, "expected `>` after `~`"));
                    }
                }
                b'>' if self.peek() == Some(b'>') && self.peek2() == Some(b'>') => {
                    self.advance();
                    self.advance();
                    Token::Seq
                }
                b'>' if self.peek() == Some(b'=') => {
                    self.advance();
                    Token::Ident(">=".to_string())
                }
                b'>' => Token::Ident(">".to_string()),
                b'<' if self.peek() == Some(b'=') => {
                    self.advance();
                    Token::Ident("<=".to_string())
                }
                b'<' => Token::Ident("<".to_string()),
                b'*' if self.peek() == Some(b'*') && self.peek2() == Some(b'*') => {
                    self.advance();
                    self.advance();
                    Token::Product
                }
                b'*' => Token::Ident("*".to_string()),
                b'/' => Token::Ident("/".to_string()),
                b'+' => Token::Ident("+".to_string()),
                b'-' if self.peek() == Some(b'-') => {
                    // Should have been consumed as a comment in skip_ws, but
                    // handle defensively: treat as `-`.
                    Token::Ident("-".to_string())
                }
                b'-' => Token::Ident("-".to_string()),
                b'!' if self.peek() == Some(b'=') => {
                    self.advance();
                    Token::Ident("!=".to_string())
                }
                b'!' => Token::Ident("!".to_string()),
                b'=' if self.peek() == Some(b'=') => {
                    self.advance();
                    Token::Ident("==".to_string())
                }
                b'=' => Token::Assign,
                b'&' if self.peek() == Some(b'&') && self.peek2() == Some(b'&') => {
                    self.advance();
                    self.advance();
                    Token::FanOut
                }
                b'&' if self.peek() == Some(b'&') => {
                    self.advance();
                    Token::Ident("&&".to_string())
                }
                b'|' if self.peek() == Some(b'|') && self.peek2() == Some(b'|') => {
                    self.advance();
                    self.advance();
                    Token::Choice
                }
                b'|' if self.peek() == Some(b'|') => {
                    self.advance();
                    Token::Ident("||".to_string())
                }
                b'?' => {
                    if self.peek() == Some(b'?') {
                        self.advance();
                        Token::Nullish
                    } else if self.peek() == Some(b'.') {
                        self.advance();
                        Token::OptChain
                    } else {
                        return Err(self.err(start_line, start_col, "expected `??` or `?.`"));
                    }
                }
                b'.' => {
                    if self.peek() == Some(b'.') && self.peek2() == Some(b'.') {
                        self.advance();
                        self.advance();
                        Token::Ellipsis
                    } else {
                        Token::Dot
                    }
                }
                b':' => Token::Colon,
                b',' => Token::Comma,
                b';' => Token::Semicolon,
                b'[' => Token::LBrack,
                b']' => Token::RBrack,
                b'{' => Token::LBrace,
                b'}' => Token::RBrace,
                b'(' => Token::LParen,
                b')' => Token::RParen,
                b'|' => Token::Pipe,
                _ => return Err(self.err(start_line, start_col, &format!("unexpected char `{}`", c as char))),
            };
            Ok(tok)
        }

        fn err(&self, line: usize, col: usize, msg: &str) -> LexError {
            LexError { msg: msg.to_string(), line, col }
        }

        fn lex_number(&mut self, line: usize, col: usize) -> Result<Token, LexError> {
            let start = self.pos;
            while let Some(c) = self.peek() {
                if c.is_ascii_digit() {
                    self.advance();
                } else {
                    break;
                }
            }
            let mut is_float = false;
            if self.peek() == Some(b'.') && self.peek2().map_or(false, |c| c.is_ascii_digit()) {
                is_float = true;
                self.advance(); // .
                while let Some(c) = self.peek() {
                    if c.is_ascii_digit() {
                        self.advance();
                    } else {
                        break;
                    }
                }
            }
            let text = std::str::from_utf8(&self.src[start..self.pos]).unwrap();
            if is_float {
                text.parse::<f64>()
                    .map(Token::Float)
                    .map_err(|_| self.err(line, col, "invalid float"))
            } else {
                text.parse::<i64>()
                    .map(Token::Int)
                    .map_err(|_| self.err(line, col, "invalid integer"))
            }
        }

        fn lex_ident(&mut self, line: usize, col: usize) -> Result<Token, LexError> {
            // `_` alone is Wild; `_foo` is an ident.
            if self.peek() == Some(b'_')
                && self.peek2().map_or(true, |c| !is_ident_cont(c))
            {
                self.advance(); // consume `_`
                return Ok(Token::Wild);
            }
            let start = self.pos;
            while let Some(c) = self.peek() {
                if is_ident_cont(c) {
                    self.advance();
                } else {
                    break;
                }
            }
            let text = std::str::from_utf8(&self.src[start..self.pos]).unwrap().to_string();
            Ok(match text.as_str() {
                "if" => Token::KwIf,
                "else" => Token::KwElse,
                "match" => Token::KwMatch,
                "rec" => Token::KwRec,
                "while" => Token::KwWhile,
                "do" => Token::KwDo,
                "for" => Token::KwFor,
                "in" => Token::KwIn,
                "return" => Token::KwReturn,
                "import" => Token::KwImport,
                "export" => Token::KwExport,
                "from" => Token::KwFrom,
                "as" => Token::KwAs,
                "infer" => Token::KwInfer,
                "type" => Token::KwType,
                "true" => Token::KwTrue,
                "false" => Token::KwFalse,
                "handle" => Token::KwHandle,
                "with" => Token::KwWith,
                "law" => Token::KwLaw,
                "forall" => Token::KwForall,
                _ => Token::Ident(text),
            })
        }

        fn lex_string(&mut self, line: usize, col: usize) -> Result<Token, LexError> {
            self.advance(); // opening "
            let mut s = String::new();
            loop {
                match self.peek() {
                    None => return Err(self.err(line, col, "unterminated string")),
                    Some(b'"') => {
                        self.advance();
                        break;
                    }
                    Some(b'\\') => {
                        self.advance();
                        match self.peek() {
                            Some(b'n') => {
                                s.push('\n');
                                self.advance();
                            }
                            Some(b't') => {
                                s.push('\t');
                                self.advance();
                            }
                            Some(b'"') => {
                                s.push('"');
                                self.advance();
                            }
                            Some(b'\\') => {
                                s.push('\\');
                                self.advance();
                            }
                            Some(c) => {
                                s.push(c as char);
                                self.advance();
                            }
                            None => return Err(self.err(line, col, "unterminated escape")),
                        }
                    }
                    Some(c) => {
                        s.push(c as char);
                        self.advance();
                    }
                }
            }
            Ok(Token::Str(s))
        }

        pub fn tokenize(mut self) -> Result<Vec<Token>, LexError> {
            let mut out = Vec::new();
            loop {
                let t = self.next_token()?;
                let is_eof = t == Token::Eof;
                out.push(t);
                if is_eof {
                    break;
                }
            }
            Ok(out)
        }
    }
}

// ============================================================================
// Module: ast
// ============================================================================

pub mod ast {
    #[derive(Debug, Clone, PartialEq)]
    pub enum Lit {
        Int(i64),
        Float(f64),
        Str(String),
        Bool(bool),
    }

    #[derive(Debug, Clone, PartialEq)]
    pub struct Program {
        pub imports: Vec<Import>,
        pub exports: Vec<Export>,
        pub bindings: Vec<Binding>,
    }

    #[derive(Debug, Clone, PartialEq)]
    pub enum Import {
        /// import name1, name2 from "path"   (with optional per-name rename)
        Names { specs: Vec<ImportSpec>, path: String },
        /// import "path" as alias
        Whole { path: String, alias: String },
    }

    #[derive(Debug, Clone, PartialEq)]
    pub struct ImportSpec {
        pub name: String,  // field to project
        pub local: String, // local binding name (== name if no `as`)
    }

    #[derive(Debug, Clone, PartialEq)]
    pub enum Export {
        /// export name   /   export name1, name2
        Names { names: Vec<String> },
        /// export name = expr   /   export name1 = e1, name2 = e2  (binding+export)
        Bindings { bindings: Vec<Binding> },
        /// export *
        All,
        /// export name from "path"   /   export name1, name2 from "path"
        NamesFrom { names: Vec<String>, path: String },
        /// export * from "path"
        AllFrom { path: String },
    }

    #[derive(Debug, Clone, PartialEq)]
    pub struct Binding {
        pub name: String,
        pub ty: Option<Type>,
        pub value: Expr,
    }

    #[derive(Debug, Clone, PartialEq)]
    pub enum Expr {
        Var(String),
        Lit(Lit),
        Wild, // `_` (valid in pattern/infer position; lint rejects elsewhere)
        Arrow { pat: Box<Pattern>, body: Box<Expr>, braced: bool },
        App { f: Box<Expr>, arg: Box<Expr> },
        Compose { l: Box<Expr>, r: Box<Expr> },   // >>>
        Product { l: Box<Expr>, r: Box<Expr> },   // ***
        FanOut { l: Box<Expr>, r: Box<Expr> },    // &&&
        Choice { l: Box<Expr>, r: Box<Expr> },    // |||
        BinOp { op: String, l: Box<Expr>, r: Box<Expr> }, // library arithmetic
        Nullish { l: Box<Expr>, r: Box<Expr> },   // ??
        OptChain { src: Box<Expr>, field: String }, // ?.
        Field { src: Box<Expr>, name: String },   // .
        Index { src: Box<Expr>, idx: Box<Expr> },  // []
        Record { fields: Vec<RecordField> },
        Tuple { items: Vec<Expr> }, // [...] positional
        Spread { value: Box<Expr> }, // ...expr (only inside Tuple)
        Match { scrutinee: Box<Expr>, arms: Vec<MatchArm> },
        If { cond: Box<Expr>, then: Box<Expr>, else_: Box<Expr> },
        MultiIf { arms: Vec<GuardArm> },
        While { cond: Box<Expr>, body: Box<Expr>, braced: bool },
        DoWhile { body: Box<Expr>, cond: Box<Expr> },
        For { var: String, iter: Box<Expr>, acc: Option<(String, Box<Expr>)>, body: Box<Expr> },
        Rec { body: Box<Expr> }, // rec { block }
        Return { value: Box<Expr> },
        Block { bindings: Vec<Binding>, trailing: Option<Box<Expr>> },
        Infer { inner: InferKind },
        Paren { inner: Box<Expr> },
        /// handle <body> with <target> = <impl>  (ADR-0076 handler installation)
        Handle {
            body: Box<Expr>,
            target: String,    // capability/bundle name (e.g. "map", "Functor<List>")
            impl_: Box<Expr>,  // the impl arrow/bundle
        },
        /// law <name>: [forall <vars>.] <lhs> = <rhs>  (ADR-0076 law declaration)
        Law {
            name: String,
            vars: Vec<String>,      // universally quantified variables (empty if no forall)
            lhs: Box<Expr>,         // left-hand side of the equation
            rhs: Box<Expr>,         // right-hand side of the equation
        },
    }

    #[derive(Debug, Clone, PartialEq)]
    pub enum InferKind {
        Name(String),       // infer x
        Arrow(Box<Expr>),   // infer (parse _)
    }

    #[derive(Debug, Clone, PartialEq)]
    pub enum RecordField {
        Named { name: String, value: Box<Expr> },     // name: value
        Shorthand { name: String },                    // name
        Computed { key: Box<Expr>, value: Box<Expr> }, // [key]: value
        Spread { value: Box<Expr> },                   // ...value
    }

    #[derive(Debug, Clone, PartialEq)]
    pub struct MatchArm {
        pub pat: Pattern,
        pub body: Box<Expr>,
    }

    #[derive(Debug, Clone, PartialEq)]
    pub struct GuardArm {
        pub cond: Box<Expr>,
        pub catch_all: bool, // `_` arm
        pub body: Box<Expr>,
    }

    #[derive(Debug, Clone, PartialEq)]
    pub enum Pattern {
        PVar(String),
        PWild,
        PLit(Lit),
        PRest(String),                              // ...name
        PRecord { elements: Vec<PatternElement> },
        PTuple { items: Vec<Pattern> },
        PConstruct { tag: String, args: Vec<Pattern> }, // some x, none
    }

    #[derive(Debug, Clone, PartialEq)]
    pub enum PatternElement {
        Rename { source: String, local: String }, // source: local  (local is a var)
        Shorthand { name: String },               // name
        Nested { source: String, pat: Box<Pattern> }, // source: { nested }
        Rest { name: String },                    // ...name
        Lit { source: String, lit: Lit },         // source: literal
    }

    #[derive(Debug, Clone, PartialEq)]
    pub enum Type {
        TVar(String),
        TNamed(String),          // Int, Str, ... (or type.Int)
        TArrow(Box<Type>, Box<Type>), // ~>
        TProd(Box<Type>, Box<Type>),
        TSum(Box<Type>, Box<Type>),
        TRecord { fields: Vec<(String, Type)>, rest: Option<String> },
        TTuple(Vec<Type>),
    }
}

// ============================================================================
// Module: parser
// ============================================================================

pub mod parser {
    use super::lexer::Token;
    use super::ast::*;

    #[derive(Debug, Clone, PartialEq)]
    pub struct ParseError {
        pub msg: String,
        pub line: usize,
        pub col: usize,
    }

    impl std::fmt::Display for ParseError {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "parse error at {}:{}: {}", self.line, self.col, self.msg)
        }
    }

    pub struct Parser {
        toks: Vec<Token>,
        pos: usize,
        // Lines/cols aligned with toks; we approximate using a parallel vec.
        lines: Vec<usize>,
        cols: Vec<usize>,
        // When true, `{` is treated as a terminator (not application). Used in
        // cond positions of while/if/for/match where `{` opens a block (ID.11).
        brace_terminator: bool,
        // When true, an Ident followed by `=` or `:` terminates the current
        // expression (a new binding is starting). Used at the top level and
        // inside blocks so that `a = f b\nc = g` doesn't parse as `a = f b c`.
        binding_terminator: bool,
    }

    /// Arithmetic operator tokens are encoded as Ident in the lexer; this set
    /// recognises them at the arithmetic precedence level (grammar §3.2 level 6).
    const ARITH_OPS: &[&str] = &[
        "+", "-", "*", "/", "==", "!=", "<", ">", "<=", ">=", "&&", "||", "!",
    ];

    fn is_atom_start(t: &Token) -> bool {
        matches!(
            t,
            Token::Ident(_)
                | Token::Int(_)
                | Token::Float(_)
                | Token::Str(_)
                | Token::Wild
                | Token::LParen
                | Token::LBrack
                | Token::LBrace
                | Token::KwIf
                | Token::KwMatch
                | Token::KwWhile
                | Token::KwDo
                | Token::KwFor
                | Token::KwRec
                | Token::KwReturn
                | Token::KwInfer
                | Token::KwTrue
                | Token::KwFalse
                | Token::KwHandle
                | Token::KwLaw
        )
    }

    impl Parser {
        pub fn new(toks: Vec<Token>, lines: Vec<usize>, cols: Vec<usize>) -> Self {
            Parser { toks, pos: 0, lines, cols, brace_terminator: false, binding_terminator: false }
        }

        fn peek(&self) -> &Token {
            &self.toks[self.pos]
        }
        fn peek_at(&self, off: usize) -> &Token {
            if self.pos + off < self.toks.len() {
                &self.toks[self.pos + off]
            } else {
                &self.toks[self.toks.len() - 1]
            }
        }
        fn advance(&mut self) -> Token {
            let t = self.toks[self.pos].clone();
            if self.pos + 1 < self.toks.len() {
                self.pos += 1;
            }
            t
        }
        fn at_eof(&self) -> bool {
            *self.peek() == Token::Eof
        }
        fn err(&self, msg: &str) -> ParseError {
            ParseError {
                msg: msg.to_string(),
                line: self.lines[self.pos],
                col: self.cols[self.pos],
            }
        }
        fn expect(&mut self, t: &Token) -> Result<(), ParseError> {
            if self.peek() == t {
                self.advance();
                Ok(())
            } else {
                Err(self.err(&format!("expected {:?}, got {:?}", t, self.peek())))
            }
        }

        fn skip_separators(&mut self) {
            while *self.peek() == Token::Comma || *self.peek() == Token::Semicolon {
                self.advance();
            }
        }

        /// Whether the upcoming token is an arithmetic operator (level 6).
        fn arith_op(&self) -> Option<&'static str> {
            if let Token::Ident(s) = self.peek() {
                for op in ARITH_OPS {
                    if s == *op {
                        return Some(op);
                    }
                }
            }
            None
        }

        // ------------------------------------------------------------------
        // Program
        // ------------------------------------------------------------------

        pub fn parse_program(&mut self) -> Result<Program, ParseError> {
            let mut imports = Vec::new();
            let mut exports = Vec::new();
            let mut bindings = Vec::new();
            while !self.at_eof() {
                self.skip_separators();
                if self.at_eof() {
                    break;
                }
                if *self.peek() == Token::KwImport {
                    imports.push(self.parse_import()?);
                } else if *self.peek() == Token::KwExport {
                    exports.push(self.parse_export()?);
                } else if self.is_binding_start() {
                    self.binding_terminator = true;
                    let b = self.parse_binding()?;
                    self.binding_terminator = false;
                    bindings.push(b);
                } else {
                    return Err(self.err("expected import, export, or binding at top level"));
                }
                self.skip_separators();
            }
            Ok(Program { imports, exports, bindings })
        }

        fn parse_import(&mut self) -> Result<Import, ParseError> {
            self.expect(&Token::KwImport)?;
            // import "path" as alias
            if let Token::Str(path) = self.peek().clone() {
                self.advance();
                self.expect(&Token::KwAs)?;
                let alias = self.parse_ident()?;
                return Ok(Import::Whole { path, alias });
            }
            // import spec (, spec)* from "path"
            let mut specs = Vec::new();
            specs.push(self.parse_import_spec()?);
            while *self.peek() == Token::Comma {
                self.advance();
                specs.push(self.parse_import_spec()?);
            }
            self.expect(&Token::KwFrom)?;
            let path = match self.advance() {
                Token::Str(s) => s,
                other => return Err(self.err(&format!("expected string path, got {:?}", other))),
            };
            Ok(Import::Names { specs, path })
        }

        fn parse_import_spec(&mut self) -> Result<ImportSpec, ParseError> {
            let name = self.parse_ident()?;
            let local = if *self.peek() == Token::KwAs {
                self.advance();
                self.parse_ident()?
            } else {
                name.clone()
            };
            Ok(ImportSpec { name, local })
        }

        fn parse_export(&mut self) -> Result<Export, ParseError> {
            self.expect(&Token::KwExport)?;
            // export *  /  export * from "path"
            if *self.peek() == Token::Ident("*".to_string()) {
                self.advance();
                if *self.peek() == Token::KwFrom {
                    self.advance();
                    let path = match self.advance() {
                        Token::Str(s) => s,
                        other => return Err(self.err(&format!("expected string path, got {:?}", other))),
                    };
                    return Ok(Export::AllFrom { path });
                }
                return Ok(Export::All);
            }
            // export spec (, spec)*   with optional `from "path"`
            // spec ::= ident ( = expr )?
            // Parse first spec to determine form.
            let mut names: Vec<String> = Vec::new();
            let mut bindings: Vec<Binding> = Vec::new();
            let mut has_binding = false;
            loop {
                let name = self.parse_ident()?;
                if *self.peek() == Token::Assign {
                    has_binding = true;
                    self.advance();
                    let value = self.parse_expr(0)?;
                    bindings.push(Binding { name, ty: None, value });
                } else {
                    names.push(name);
                }
                if *self.peek() == Token::Comma {
                    self.advance();
                    continue;
                }
                break;
            }
            // Re-export form: export name1, name2 from "path"
            if *self.peek() == Token::KwFrom {
                if has_binding {
                    return Err(self.err("cannot combine `= expr` with `from` in export"));
                }
                self.advance();
                let path = match self.advance() {
                    Token::Str(s) => s,
                    other => return Err(self.err(&format!("expected string path, got {:?}", other))),
                };
                return Ok(Export::NamesFrom { names, path });
            }
            // Consistency: if any spec has `= expr`, all must (enforced by the
            // loop above — bare names go into `names`, bindings into `bindings`).
            // If mixed, we reject to keep it simple and unambiguous.
            if has_binding && !names.is_empty() {
                return Err(self.err("cannot mix `name` and `name = expr` in one export; split into separate declarations"));
            }
            if has_binding {
                Ok(Export::Bindings { bindings })
            } else {
                Ok(Export::Names { names })
            }
        }

        fn parse_ident(&mut self) -> Result<String, ParseError> {
            match self.advance() {
                Token::Ident(s) => Ok(s),
                other => Err(self.err(&format!("expected identifier, got {:?}", other))),
            }
        }

        /// Lookahead: is this a binding (`name =` or `name: Type =`)?
        fn is_binding_start(&self) -> bool {
            if let Token::Ident(_) = self.peek() {
                // name =
                if *self.peek_at(1) == Token::Assign {
                    return true;
                }
                // name: Type =
                if *self.peek_at(1) == Token::Colon {
                    return true;
                }
            }
            false
        }

        fn parse_binding(&mut self) -> Result<Binding, ParseError> {
            let name = self.parse_ident()?;
            let ty = if *self.peek() == Token::Colon {
                self.advance();
                Some(self.parse_type()?)
            } else {
                None
            };
            self.expect(&Token::Assign)?;
            let value = self.parse_expr(0)?;
            Ok(Binding { name, ty, value })
        }

        // ------------------------------------------------------------------
        // Types (minimal)
        // ------------------------------------------------------------------

        fn parse_type(&mut self) -> Result<Type, ParseError> {
            self.parse_type_arrow()
        }

        fn parse_type_arrow(&mut self) -> Result<Type, ParseError> {
            let left = self.parse_type_atom()?;
            if *self.peek() == Token::Arrow {
                self.advance();
                let right = self.parse_type_arrow()?;
                Ok(Type::TArrow(Box::new(left), Box::new(right)))
            } else {
                Ok(left)
            }
        }

        fn parse_type_atom(&mut self) -> Result<Type, ParseError> {
            match self.advance() {
                Token::Ident(s) => {
                    // type.Int or Int
                    let name = if s == "type" {
                        // type.Name
                        self.expect(&Token::Dot)?;
                        self.parse_ident()?
                    } else {
                        s
                    };
                    Ok(Type::TNamed(name))
                }
                Token::LParen => {
                    let t = self.parse_type()?;
                    self.expect(&Token::RParen)?;
                    Ok(t)
                }
                Token::LBrack => {
                    let mut items = Vec::new();
                    if *self.peek() != Token::RBrack {
                        items.push(self.parse_type()?);
                        while *self.peek() == Token::Comma {
                            self.advance();
                            items.push(self.parse_type()?);
                        }
                    }
                    self.expect(&Token::RBrack)?;
                    Ok(Type::TTuple(items))
                }
                Token::LBrace => {
                    let mut fields = Vec::new();
                    let mut rest = None;
                    if *self.peek() != Token::RBrace {
                        loop {
                            if *self.peek() == Token::Ellipsis {
                                self.advance();
                                rest = Some(self.parse_ident()?);
                            } else {
                                let n = self.parse_ident()?;
                                self.expect(&Token::Colon)?;
                                let ty = self.parse_type()?;
                                fields.push((n, ty));
                            }
                            if *self.peek() == Token::Comma {
                                self.advance();
                            } else {
                                break;
                            }
                        }
                    }
                    self.expect(&Token::RBrace)?;
                    Ok(Type::TRecord { fields, rest })
                }
                other => Err(self.err(&format!("expected type, got {:?}", other))),
            }
        }

        // ------------------------------------------------------------------
        // Expressions (Pratt)
        // ------------------------------------------------------------------

        pub fn parse_expr(&mut self, rbp: u8) -> Result<Expr, ParseError> {
            let mut left = self.parse_prefix()?;
            loop {
                let op_lbp = self.infix_lbp(&left);
                if let Some(lbp) = op_lbp {
                    if lbp > rbp {
                        left = self.parse_infix(left, lbp)?;
                        continue;
                    }
                }
                break;
            }
            Ok(left)
        }

        /// Compute the infix left-binding-power of the upcoming token, given
        /// the already-parsed left operand. Application (juxtaposition) is
        /// triggered by an atom-start token following an operand.
        fn infix_lbp(&self, _left: &Expr) -> Option<u8> {
            let t = self.peek();
            // Explicit operator tokens.
            if let Some(lbp) = t.lbp() {
                return Some(lbp);
            }
            // Arithmetic (library) operators encoded as Ident.
            if self.arith_op().is_some() {
                return Some(70);
            }
            // Application (juxtaposition): an atom-start token in operand
            // position. Not triggered after a prefix-only context, but for
            // the reference parser we treat any atom-start as application.
            if is_atom_start(t) {
                // ID.11: in cond positions, `{` opens a block, not application.
                // For `for x in iter, acc = init`, `,` also terminates iter.
                if self.brace_terminator && (*t == Token::LBrace || *t == Token::Comma) {
                    return None;
                }
                // A new binding (`name =` or `name:`) terminates the expression.
                if self.binding_terminator {
                    if let Token::Ident(_) = t {
                        let nxt = self.peek_at(1);
                        if *nxt == Token::Assign || *nxt == Token::Colon {
                            return None;
                        }
                    }
                }
                return Some(80);
            }
            None
        }

        fn parse_infix(&mut self, left: Expr, lbp: u8) -> Result<Expr, ParseError> {
            let t = self.peek().clone();
            match t {
                Token::Dot => {
                    self.advance();
                    let name = self.parse_ident()?;
                    Ok(Expr::Field { src: Box::new(left), name })
                }
                Token::LBrack => {
                    self.advance();
                    let idx = self.parse_expr(0)?;
                    self.expect(&Token::RBrack)?;
                    Ok(Expr::Index { src: Box::new(left), idx: Box::new(idx) })
                }
                Token::OptChain => {
                    self.advance();
                    let name = self.parse_ident()?;
                    Ok(Expr::OptChain { src: Box::new(left), field: name })
                }
                Token::Nullish => {
                    self.advance();
                    let r = self.parse_expr(59)?;
                    Ok(Expr::Nullish { l: Box::new(left), r: Box::new(r) })
                }
                Token::Product => {
                    self.advance();
                    let r = self.parse_expr(49)?;
                    Ok(Expr::Product { l: Box::new(left), r: Box::new(r) })
                }
                Token::FanOut => {
                    self.advance();
                    let r = self.parse_expr(49)?;
                    Ok(Expr::FanOut { l: Box::new(left), r: Box::new(r) })
                }
                Token::Seq => {
                    self.advance();
                    let r = self.parse_expr(39)?;
                    Ok(Expr::Compose { l: Box::new(left), r: Box::new(r) })
                }
                Token::Choice => {
                    self.advance();
                    let r = self.parse_expr(29)?;
                    Ok(Expr::Choice { l: Box::new(left), r: Box::new(r) })
                }
                Token::Arrow => {
                    self.advance();
                    // `~>` is right-associative; LHS is a pattern.
                    let pat = self.expr_to_pattern(left)?;
                    let braced = *self.peek() == Token::LBrace;
                    let body = if braced {
                        self.advance(); // {
                        let b = self.parse_block_body()?;
                        self.expect(&Token::RBrace)?;
                        b
                    } else {
                        self.parse_expr(21)?
                    };
                    Ok(Expr::Arrow { pat: Box::new(pat), body: Box::new(body), braced })
                }
                Token::Ident(_) if self.arith_op().is_some() => {
                    let op = self.arith_op().unwrap().to_string();
                    self.advance();
                    let r = self.parse_expr(69)?;
                    Ok(Expr::BinOp { op, l: Box::new(left), r: Box::new(r) })
                }
                _ if is_atom_start(self.peek()) => {
                    // Application (juxtaposition).
                    let arg = self.parse_expr(79)?;
                    Ok(Expr::App { f: Box::new(left), arg: Box::new(arg) })
                }
                _ => Err(self.err("expected infix operator")),
            }
        }

        fn parse_prefix(&mut self) -> Result<Expr, ParseError> {
            let t = self.peek().clone();
            match t {
                Token::Int(n) => {
                    self.advance();
                    Ok(Expr::Lit(Lit::Int(n)))
                }
                Token::Float(n) => {
                    self.advance();
                    Ok(Expr::Lit(Lit::Float(n)))
                }
                Token::Str(s) => {
                    self.advance();
                    Ok(Expr::Lit(Lit::Str(s)))
                }
                Token::KwTrue => {
                    self.advance();
                    Ok(Expr::Lit(Lit::Bool(true)))
                }
                Token::KwFalse => {
                    self.advance();
                    Ok(Expr::Lit(Lit::Bool(false)))
                }
                Token::Wild => {
                    self.advance();
                    Ok(Expr::Wild)
                }
                Token::Ident(s) => {
                    // Point-free prefix operator? e.g. `* 2`, `+ 1`, `.name`.
                    if ARITH_OPS.contains(&s.as_str()) {
                        self.advance();
                        // prefix operator = point-free arrow: x ~> x <op> rhs
                        let rhs = self.parse_expr(69)?;
                        let op = s;
                        // Desugar to: x ~> (x <op> rhs)
                        let pat = Pattern::PVar("_arg".to_string());
                        let body = Expr::BinOp {
                            op,
                            l: Box::new(Expr::Var("_arg".to_string())),
                            r: Box::new(rhs),
                        };
                        return Ok(Expr::Arrow {
                            pat: Box::new(pat),
                            body: Box::new(body),
                            braced: false,
                        });
                    }
                    self.advance();
                    Ok(Expr::Var(s))
                }
                Token::LParen => {
                    self.advance();
                    let e = self.parse_expr(0)?;
                    self.expect(&Token::RParen)?;
                    Ok(Expr::Paren { inner: Box::new(e) })
                }
                Token::LBrack => self.parse_tuple(),
                Token::LBrace => self.parse_record(),
                Token::KwIf => self.parse_if(),
                Token::KwMatch => self.parse_match(),
                Token::KwWhile => self.parse_while(),
                Token::KwDo => self.parse_do_while(),
                Token::KwFor => self.parse_for(),
                Token::KwRec => self.parse_rec(),
                Token::KwReturn => {
                    self.advance();
                    let v = self.parse_expr(0)?;
                    Ok(Expr::Return { value: Box::new(v) })
                }
                Token::KwInfer => self.parse_infer(),
                Token::KwHandle => self.parse_handle(),
                Token::KwLaw => self.parse_law(),
                other => Err(self.err(&format!("unexpected token in expression: {:?}", other))),
            }
        }

        fn parse_tuple(&mut self) -> Result<Expr, ParseError> {
            self.expect(&Token::LBrack)?;
            let mut items = Vec::new();
            if *self.peek() != Token::RBrack {
                items.push(self.parse_tuple_item()?);
                while *self.peek() == Token::Comma {
                    self.advance();
                    if *self.peek() == Token::RBrack {
                        break;
                    }
                    items.push(self.parse_tuple_item()?);
                }
            }
            self.expect(&Token::RBrack)?;
            Ok(Expr::Tuple { items })
        }

        fn parse_tuple_item(&mut self) -> Result<Expr, ParseError> {
            if *self.peek() == Token::Ellipsis {
                self.advance();
                let v = self.parse_expr(0)?;
                Ok(Expr::Spread { value: Box::new(v) })
            } else {
                self.parse_expr(0)
            }
        }

        fn parse_record(&mut self) -> Result<Expr, ParseError> {
            self.expect(&Token::LBrace)?;
            let mut fields = Vec::new();
            while *self.peek() != Token::RBrace {
                self.skip_separators();
                if *self.peek() == Token::RBrace {
                    break;
                }
                let f = self.parse_record_field()?;
                fields.push(f);
                self.skip_separators();
            }
            self.expect(&Token::RBrace)?;
            Ok(Expr::Record { fields })
        }

        fn parse_record_field(&mut self) -> Result<RecordField, ParseError> {
            if *self.peek() == Token::Ellipsis {
                self.advance();
                let v = self.parse_expr(0)?;
                return Ok(RecordField::Spread { value: Box::new(v) });
            }
            if *self.peek() == Token::LBrack {
                // computed key
                self.advance();
                let key = self.parse_expr(0)?;
                self.expect(&Token::RBrack)?;
                self.expect(&Token::Colon)?;
                let value = self.parse_expr(0)?;
                return Ok(RecordField::Computed { key: Box::new(key), value: Box::new(value) });
            }
            // ident
            let name = self.parse_ident()?;
            if *self.peek() == Token::Colon {
                self.advance();
                let value = self.parse_expr(0)?;
                Ok(RecordField::Named { name, value: Box::new(value) })
            } else {
                Ok(RecordField::Shorthand { name })
            }
        }

        fn parse_if(&mut self) -> Result<Expr, ParseError> {
            self.expect(&Token::KwIf)?;
            self.brace_terminator = true;
            let cond = self.parse_expr(0)?;
            self.brace_terminator = false;
            if *self.peek() == Token::Colon {
                // multi-way if: `if c1: e1, c2: e2, _: e3`
                self.advance();
                let first_body = self.parse_expr(0)?;
                let mut arms = vec![GuardArm {
                    cond: Box::new(cond),
                    catch_all: false,
                    body: Box::new(first_body),
                }];
                loop {
                    self.skip_separators();
                    if *self.peek() == Token::Wild {
                        self.advance();
                        self.expect(&Token::Colon)?;
                        let body = self.parse_expr(0)?;
                        arms.push(GuardArm {
                            cond: Box::new(Expr::Lit(Lit::Bool(true))),
                            catch_all: true,
                            body: Box::new(body),
                        });
                        break;
                    }
                    if !is_atom_start(self.peek()) {
                        break;
                    }
                    let c = self.parse_expr(0)?;
                    self.expect(&Token::Colon)?;
                    let body = self.parse_expr(0)?;
                    arms.push(GuardArm { cond: Box::new(c), catch_all: false, body: Box::new(body) });
                }
                return Ok(Expr::MultiIf { arms });
            }
            // two-branch if
            let then = self.parse_branch()?;
            self.expect(&Token::KwElse)?;
            let else_ = self.parse_branch()?;
            Ok(Expr::If { cond: Box::new(cond), then: Box::new(then), else_: Box::new(else_) })
        }

        fn parse_branch(&mut self) -> Result<Expr, ParseError> {
            if *self.peek() == Token::LBrace {
                self.advance();
                let b = self.parse_block_body()?;
                self.expect(&Token::RBrace)?;
                Ok(b)
            } else {
                self.parse_expr(0)
            }
        }

        fn parse_match(&mut self) -> Result<Expr, ParseError> {
            self.expect(&Token::KwMatch)?;
            self.brace_terminator = true;
            let scrutinee = self.parse_expr(0)?;
            self.brace_terminator = false;
            self.expect(&Token::LBrace)?;
            let mut arms = Vec::new();
            while *self.peek() != Token::RBrace {
                self.skip_separators();
                if *self.peek() == Token::RBrace {
                    break;
                }
                let pat = self.parse_pattern()?;
                self.expect(&Token::Colon)?;
                let body = self.parse_expr(0)?;
                arms.push(MatchArm { pat, body: Box::new(body) });
                self.skip_separators();
            }
            self.expect(&Token::RBrace)?;
            Ok(Expr::Match { scrutinee: Box::new(scrutinee), arms })
        }

        fn parse_while(&mut self) -> Result<Expr, ParseError> {
            self.expect(&Token::KwWhile)?;
            self.brace_terminator = true;
            let cond = self.parse_expr(0)?;
            self.brace_terminator = false;
            if *self.peek() == Token::LBrace {
                self.advance();
                let body = self.parse_block_body()?;
                self.expect(&Token::RBrace)?;
                Ok(Expr::While { cond: Box::new(cond), body: Box::new(body), braced: true })
            } else {
                let body = self.parse_expr(0)?;
                Ok(Expr::While { cond: Box::new(cond), body: Box::new(body), braced: false })
            }
        }

        fn parse_do_while(&mut self) -> Result<Expr, ParseError> {
            self.expect(&Token::KwDo)?;
            self.expect(&Token::LBrace)?;
            let body = self.parse_block_body()?;
            self.expect(&Token::RBrace)?;
            self.expect(&Token::KwWhile)?;
            let cond = self.parse_expr(0)?;
            Ok(Expr::DoWhile { body: Box::new(body), cond: Box::new(cond) })
        }

        fn parse_for(&mut self) -> Result<Expr, ParseError> {
            self.expect(&Token::KwFor)?;
            let var = self.parse_ident()?;
            self.expect(&Token::KwIn)?;
            self.brace_terminator = true;
            let iter = self.parse_expr(0)?;
            self.brace_terminator = false;
            let acc = if *self.peek() == Token::Comma {
                self.advance();
                let acc_name = self.parse_ident()?;
                self.expect(&Token::Assign)?;
                self.brace_terminator = true;
                let init = self.parse_expr(0)?;
                self.brace_terminator = false;
                Some((acc_name, Box::new(init)))
            } else {
                None
            };
            self.expect(&Token::LBrace)?;
            let body = self.parse_block_body()?;
            self.expect(&Token::RBrace)?;
            Ok(Expr::For { var, iter: Box::new(iter), acc, body: Box::new(body) })
        }

        fn parse_rec(&mut self) -> Result<Expr, ParseError> {
            self.expect(&Token::KwRec)?;
            self.expect(&Token::LBrace)?;
            let body = self.parse_block_body()?;
            self.expect(&Token::RBrace)?;
            Ok(Expr::Rec { body: Box::new(body) })
        }

        fn parse_infer(&mut self) -> Result<Expr, ParseError> {
            self.expect(&Token::KwInfer)?;
            if *self.peek() == Token::LParen {
                self.advance();
                let e = self.parse_expr(0)?;
                self.expect(&Token::RParen)?;
                Ok(Expr::Infer { inner: InferKind::Arrow(Box::new(e)) })
            } else {
                let n = self.parse_ident()?;
                Ok(Expr::Infer { inner: InferKind::Name(n) })
            }
        }

        /// handle <body> with <target> = <impl>  (ADR-0076 handler installation)
        ///
        /// The body is parsed as a full expression (rbp 0); `with` is a keyword
        /// so it naturally terminates the body (it is neither an infix operator
        /// nor an atom-start token). The target is an identifier, optionally
        /// followed by `<type-args>` (e.g. `Functor<List>`); angle brackets are
        /// lexed as `Ident("<")` / `Ident(">")` in this lexer, so we capture
        /// them as a string suffix. For v0.1 only a single binding is supported
        /// (no comma-separated list).
        fn parse_handle(&mut self) -> Result<Expr, ParseError> {
            self.expect(&Token::KwHandle)?;
            let body = self.parse_expr(0)?;
            self.expect(&Token::KwWith)?;
            let target = self.parse_handle_target()?;
            self.expect(&Token::Assign)?;
            let impl_ = self.parse_expr(0)?;
            Ok(Expr::Handle {
                body: Box::new(body),
                target,
                impl_: Box::new(impl_),
            })
        }

        /// law <name>: [forall <vars>.] <lhs> = <rhs>  (ADR-0076 law declaration)
        ///
        /// The name is an identifier. After the colon, an optional
        /// `forall <vars>.` prefix binds universally quantified variables.
        /// Then the lhs and rhs are parsed as expressions separated by `=`.
        /// The `.` separating the quantifier from the body is `Token::Dot`
        /// (the lexer never produces `Token::Ident(".")`).
        fn parse_law(&mut self) -> Result<Expr, ParseError> {
            self.expect(&Token::KwLaw)?;
            let name = self.parse_ident()?;
            self.expect(&Token::Colon)?;

            // Optional: forall <var1> <var2> ... .
            let mut vars = Vec::new();
            if *self.peek() == Token::KwForall {
                self.advance(); // consume forall
                // Parse one or more identifiers until we hit a Dot. The lexer
                // produces Token::Dot for `.` (never Token::Ident(".")), so the
                // while-let simply stops matching when it sees the Dot.
                while let Token::Ident(s) = self.peek().clone() {
                    self.advance();
                    vars.push(s);
                }
                self.expect(&Token::Dot)?; // the . after forall vars
            }

            let lhs = self.parse_expr(0)?;
            self.expect(&Token::Assign)?;
            let rhs = self.parse_expr(0)?;

            Ok(Expr::Law {
                name,
                vars,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            })
        }

        /// Parse a handler target: an identifier optionally followed by
        /// `<type-args>` (e.g. `Functor<List>`). Angle brackets are lexed as
        /// `Ident("<")` / `Ident(">")` here, so we detect them by string value
        /// and capture everything up to the closing `>` into the target string.
        fn parse_handle_target(&mut self) -> Result<String, ParseError> {
            let name = self.parse_ident()?;
            let mut target = name;
            // Type application: Functor<List>. `<` and `>` are Ident in this lexer.
            if let Token::Ident(s) = self.peek() {
                if s == "<" {
                    self.advance(); // consume `<`
                    target.push('<');
                    // Capture type args until the matching `>`. We accept nested
                    // angle brackets and idents/commas in between.
                    let mut depth = 1;
                    loop {
                        match self.peek().clone() {
                            Token::Ident(t) if t == ">" => {
                                self.advance();
                                depth -= 1;
                                target.push('>');
                                if depth == 0 {
                                    break;
                                }
                            }
                            Token::Ident(t) if t == "<" => {
                                self.advance();
                                depth += 1;
                                target.push('<');
                            }
                            Token::Ident(t) => {
                                self.advance();
                                target.push_str(&t);
                            }
                            Token::Comma => {
                                self.advance();
                                target.push_str(", ");
                            }
                            Token::Eof => {
                                return Err(self.err("unterminated type arguments in handler target"));
                            }
                            other => {
                                return Err(self.err(&format!(
                                    "unexpected token in type arguments: {:?}",
                                    other
                                )));
                            }
                        }
                    }
                }
            }
            Ok(target)
        }

        /// Parse the body of a block `{ ... }`: a sequence of bindings with an
        /// optional trailing expression. The value is the last binding's value
        /// or the trailing expression. Caller consumes the closing `}`.
        fn parse_block_body(&mut self) -> Result<Expr, ParseError> {
            let mut bindings = Vec::new();
            let mut trailing: Option<Expr> = None;
            loop {
                self.skip_separators();
                if *self.peek() == Token::RBrace {
                    break;
                }
                if self.is_binding_start() {
                    self.binding_terminator = true;
                    let b = self.parse_binding()?;
                    self.binding_terminator = false;
                    bindings.push(b);
                } else {
                    // trailing expression
                    self.binding_terminator = true;
                    let e = self.parse_expr(0)?;
                    self.binding_terminator = false;
                    self.skip_separators();
                    if *self.peek() == Token::RBrace {
                        trailing = Some(e);
                        break;
                    }
                    // If not `}`, it might be another construct; treat as trailing.
                    trailing = Some(e);
                    break;
                }
            }
            Ok(Expr::Block { bindings, trailing: trailing.map(Box::new) })
        }

        // ------------------------------------------------------------------
        // Patterns
        // ------------------------------------------------------------------

        fn parse_pattern(&mut self) -> Result<Pattern, ParseError> {
            // Patterns are parsed by parsing an expr and converting, EXCEPT
            // for rest `...name` and constructor `tag arg`.
            if *self.peek() == Token::Ellipsis {
                self.advance();
                let name = self.parse_ident()?;
                return Ok(Pattern::PRest(name));
            }
            let e = self.parse_expr(0)?;
            self.expr_to_pattern(e)
        }

        /// Convert an expr (parsed in pattern position) into a Pattern.
        fn expr_to_pattern(&self, e: Expr) -> Result<Pattern, ParseError> {
            match e {
                Expr::Var(n) => Ok(Pattern::PVar(n)),
                Expr::Wild => Ok(Pattern::PWild),
                Expr::Lit(l) => Ok(Pattern::PLit(l)),
                Expr::Paren { inner } => self.expr_to_pattern(*inner),
                Expr::Tuple { items } => {
                    let mut pats = Vec::new();
                    for it in items {
                        pats.push(self.expr_to_pattern(it)?);
                    }
                    Ok(Pattern::PTuple { items: pats })
                }
                Expr::Record { fields } => {
                    let mut elements = Vec::new();
                    for f in fields {
                        match f {
                            RecordField::Named { name, value } => match *value {
                                Expr::Var(local) => {
                                    elements.push(PatternElement::Rename { source: name, local });
                                }
                                Expr::Wild => {
                                    elements.push(PatternElement::Shorthand { name });
                                }
                                inner => {
                                    elements.push(PatternElement::Nested {
                                        source: name,
                                        pat: Box::new(self.expr_to_pattern(inner)?),
                                    });
                                }
                            },
                            RecordField::Shorthand { name } => {
                                elements.push(PatternElement::Shorthand { name });
                            }
                            RecordField::Spread { value } => match *value {
                                Expr::Var(n) => elements.push(PatternElement::Rest { name: n }),
                                _ => return Err(self.err("rest pattern must bind a name")),
                            },
                            RecordField::Computed { .. } => {
                                return Err(self.err("computed keys not allowed in patterns"));
                            }
                        }
                    }
                    Ok(Pattern::PRecord { elements })
                }
                Expr::App { f, arg } => {
                    // Constructor pattern: `tag arg`
                    if let Expr::Var(tag) = *f {
                        let args = vec![self.expr_to_pattern(*arg)?];
                        Ok(Pattern::PConstruct { tag, args })
                    } else {
                        Err(self.err("invalid pattern (application of non-constructor)"))
                    }
                }
                other => Err(self.err(&format!("not a valid pattern: {:?}", other))),
            }
        }
    }
}

// ============================================================================
// Module: pretty
// ============================================================================

pub mod pretty {
    use super::ast::*;

    pub fn pretty_program(p: &Program) -> String {
        let mut s = String::new();
        for im in &p.imports {
            s.push_str(&pretty_import(im));
            s.push('\n');
        }
        if !p.imports.is_empty() && (!p.bindings.is_empty() || !p.exports.is_empty()) {
            s.push('\n');
        }
        // Exports and bindings may be intermixed in source, but the AST keeps
        // them in separate vecs. We print exports first (marking visibility),
        // then bindings. Round-trip is preserved because parse collects them
        // back into the same two vecs regardless of source order.
        for ex in &p.exports {
            s.push_str(&pretty_export(ex));
            s.push('\n');
        }
        if !p.exports.is_empty() && !p.bindings.is_empty() {
            s.push('\n');
        }
        for (i, b) in p.bindings.iter().enumerate() {
            if i > 0 {
                s.push('\n');
            }
            s.push_str(&pretty_binding(b));
            s.push('\n');
        }
        s
    }

    fn pretty_import(im: &Import) -> String {
        match im {
            Import::Names { specs, path } => {
                let parts: Vec<String> = specs
                    .iter()
                    .map(|sp| {
                        if sp.name == sp.local {
                            sp.name.clone()
                        } else {
                            format!("{} as {}", sp.name, sp.local)
                        }
                    })
                    .collect();
                format!("import {} from \"{}\"", parts.join(", "), path)
            }
            Import::Whole { path, alias } => {
                format!("import \"{}\" as {}", path, alias)
            }
        }
    }

    fn pretty_export(ex: &Export) -> String {
        match ex {
            Export::Names { names } => format!("export {}", names.join(", ")),
            Export::Bindings { bindings } => {
                // Each binding on its own line; join with newline (caller adds
                // a trailing newline). We emit multiple lines here.
                let parts: Vec<String> = bindings
                    .iter()
                    .map(|b| format!("export {}", pretty_binding(b)))
                    .collect();
                parts.join("\n")
            }
            Export::All => "export *".to_string(),
            Export::NamesFrom { names, path } => {
                format!("export {} from \"{}\"", names.join(", "), path)
            }
            Export::AllFrom { path } => format!("export * from \"{}\"", path),
        }
    }

    pub fn pretty_binding(b: &Binding) -> String {
        match &b.ty {
            Some(t) => format!("{}: {} = {}", b.name, pretty_type(t), pretty_expr(&b.value, 0)),
            None => format!("{} = {}", b.name, pretty_expr(&b.value, 0)),
        }
    }

    fn need_paren(e: &Expr, parent_prec: u8) -> bool {
        prec_of(e) < parent_prec
    }

    fn prec_of(e: &Expr) -> u8 {
        match e {
            Expr::Field { .. } | Expr::Index { .. } => 90,
            Expr::OptChain { .. } => 60,
            Expr::App { .. } => 80,
            Expr::BinOp { .. } => 70,
            Expr::Nullish { .. } => 60,
            Expr::Product { .. } | Expr::FanOut { .. } => 50,
            Expr::Compose { .. } => 40,
            Expr::Choice { .. } => 30,
            Expr::Arrow { .. } => 20,
            _ => 100, // atoms
        }
    }

    pub fn pretty_expr(e: &Expr, parent_prec: u8) -> String {
        let s = pretty_expr_raw(e);
        if need_paren(e, parent_prec) {
            format!("({})", s)
        } else {
            s
        }
    }

    fn pretty_expr_raw(e: &Expr) -> String {
        match e {
            Expr::Var(n) => n.clone(),
            Expr::Wild => "_".to_string(),
            Expr::Lit(l) => pretty_lit(l),
            Expr::Paren { inner } => format!("({})", pretty_expr(inner, 0)),
            Expr::Arrow { pat, body, braced } => {
                if *braced {
                    format!("{} ~> {}", pretty_pattern(pat), pretty_block(body))
                } else {
                    format!("{} ~> {}", pretty_pattern(pat), pretty_expr(body, 21))
                }
            }
            Expr::App { f, arg } => {
                format!("{} {}", pretty_expr(f, 80), pretty_expr(arg, 79))
            }
            Expr::Compose { l, r } => format!("{} >>> {}", pretty_expr(l, 40), pretty_expr(r, 39)),
            Expr::Product { l, r } => format!("{} *** {}", pretty_expr(l, 50), pretty_expr(r, 49)),
            Expr::FanOut { l, r } => format!("{} &&& {}", pretty_expr(l, 50), pretty_expr(r, 49)),
            Expr::Choice { l, r } => format!("{} ||| {}", pretty_expr(l, 30), pretty_expr(r, 29)),
            Expr::BinOp { op, l, r } => format!("{} {} {}", pretty_expr(l, 70), op, pretty_expr(r, 69)),
            Expr::Nullish { l, r } => format!("{} ?? {}", pretty_expr(l, 60), pretty_expr(r, 59)),
            Expr::OptChain { src, field } => format!("{}?.{}", pretty_expr(src, 60), field),
            Expr::Field { src, name } => format!("{}.{}", pretty_expr(src, 90), name),
            Expr::Index { src, idx } => format!("{}[{}]", pretty_expr(src, 90), pretty_expr(idx, 0)),
            Expr::Record { fields } => {
                let parts: Vec<String> = fields.iter().map(pretty_record_field).collect();
                format!("{{ {} }}", parts.join(", "))
            }
            Expr::Tuple { items } => {
                let parts: Vec<String> = items.iter().map(|i| pretty_expr(i, 0)).collect();
                format!("[{}]", parts.join(", "))
            }
            Expr::Spread { value } => format!("...{}", pretty_expr(value, 0)),
            Expr::Match { scrutinee, arms } => {
                let parts: Vec<String> = arms
                    .iter()
                    .map(|a| format!("{}: {}", pretty_pattern(&a.pat), pretty_expr(&a.body, 0)))
                    .collect();
                format!("match {} {{ {} }}", pretty_expr(scrutinee, 0), parts.join(", "))
            }
            Expr::If { cond, then, else_ } => {
                format!(
                    "if {} {} else {}",
                    pretty_expr(cond, 0),
                    pretty_branch(then),
                    pretty_branch(else_)
                )
            }
            Expr::MultiIf { arms } => {
                let parts: Vec<String> = arms
                    .iter()
                    .map(|a| {
                        if a.catch_all {
                            format!("_: {}", pretty_expr(&a.body, 0))
                        } else {
                            format!("{}: {}", pretty_expr(&a.cond, 0), pretty_expr(&a.body, 0))
                        }
                    })
                    .collect();
                format!("if {}", parts.join(", "))
            }
            Expr::While { cond, body, braced } => {
                if *braced {
                    format!("while {} {}", pretty_expr(cond, 0), pretty_block(body))
                } else {
                    format!("while {} {}", pretty_expr(cond, 0), pretty_expr(body, 0))
                }
            }
            Expr::DoWhile { body, cond } => {
                format!("do {} while {}", pretty_block(body), pretty_expr(cond, 0))
            }
            Expr::For { var, iter, acc, body } => match acc {
                Some((an, init)) => format!(
                    "for {} in {}, {} = {} {}",
                    var,
                    pretty_expr(iter, 0),
                    an,
                    pretty_expr(init, 0),
                    pretty_block(body)
                ),
                None => format!("for {} in {} {}", var, pretty_expr(iter, 0), pretty_block(body)),
            },
            Expr::Rec { body } => format!("rec {}", pretty_block(body)),
            Expr::Return { value } => format!("return {}", pretty_expr(value, 0)),
            Expr::Block { bindings, trailing } => pretty_block_inner(bindings, trailing.as_deref()),
            Expr::Infer { inner } => match inner {
                InferKind::Name(n) => format!("infer {}", n),
                InferKind::Arrow(e) => format!("infer ({})", pretty_expr(e, 0)),
            },
            Expr::Handle { body, target, impl_ } => {
                format!(
                    "handle {} with {} = {}",
                    pretty_expr(body, 0),
                    target,
                    pretty_expr(impl_, 0)
                )
            },
            Expr::Law { name, vars, lhs, rhs } => {
                let forall_part = if vars.is_empty() {
                    String::new()
                } else {
                    format!("forall {}. ", vars.join(" "))
                };
                format!(
                    "law {}: {}{} = {}",
                    name,
                    forall_part,
                    pretty_expr(lhs, 0),
                    pretty_expr(rhs, 0)
                )
            },
        }
    }

    fn pretty_lit(l: &Lit) -> String {
        match l {
            Lit::Int(n) => n.to_string(),
            Lit::Float(n) => n.to_string(),
            Lit::Str(s) => format!("\"{}\"", s),
            Lit::Bool(b) => b.to_string(),
        }
    }

    fn pretty_record_field(f: &RecordField) -> String {
        match f {
            RecordField::Named { name, value } => format!("{}: {}", name, pretty_expr(value, 0)),
            RecordField::Shorthand { name } => name.clone(),
            RecordField::Computed { key, value } => {
                format!("[{}]: {}", pretty_expr(key, 0), pretty_expr(value, 0))
            }
            RecordField::Spread { value } => format!("...{}", pretty_expr(value, 0)),
        }
    }

    fn pretty_branch(e: &Expr) -> String {
        match e {
            Expr::Block { .. } => pretty_block(e),
            _ => pretty_expr(e, 0),
        }
    }

    fn pretty_block(e: &Expr) -> String {
        match e {
            Expr::Block { bindings, trailing } => pretty_block_inner(bindings, trailing.as_deref()),
            _ => {
                // A non-block body in braced position: wrap as a single-expr block.
                format!("{{ {} }}", pretty_expr(e, 0))
            }
        }
    }

    fn pretty_block_inner(bindings: &[Binding], trailing: Option<&Expr>) -> String {
        let mut parts: Vec<String> = bindings.iter().map(pretty_binding).collect();
        if let Some(t) = trailing {
            parts.push(pretty_expr(t, 0));
        }
        if parts.is_empty() {
            "{}".to_string()
        } else {
            format!("{{ {} }}", parts.join(", "))
        }
    }

    pub fn pretty_pattern(p: &Pattern) -> String {
        match p {
            Pattern::PVar(n) => n.clone(),
            Pattern::PWild => "_".to_string(),
            Pattern::PLit(l) => pretty_lit(l),
            Pattern::PRest(n) => format!("...{}", n),
            Pattern::PRecord { elements } => {
                let parts: Vec<String> = elements.iter().map(pretty_pattern_element).collect();
                format!("{{ {} }}", parts.join(", "))
            }
            Pattern::PTuple { items } => {
                let parts: Vec<String> = items.iter().map(pretty_pattern).collect();
                format!("[{}]", parts.join(", "))
            }
            Pattern::PConstruct { tag, args } => {
                let parts: Vec<String> = args.iter().map(pretty_pattern).collect();
                if parts.is_empty() {
                    tag.clone()
                } else {
                    format!("{} {}", tag, parts.join(" "))
                }
            }
        }
    }

    fn pretty_pattern_element(e: &PatternElement) -> String {
        match e {
            PatternElement::Rename { source, local } => format!("{}: {}", source, local),
            PatternElement::Shorthand { name } => name.clone(),
            PatternElement::Nested { source, pat } => format!("{}: {}", source, pretty_pattern(pat)),
            PatternElement::Rest { name } => format!("...{}", name),
            PatternElement::Lit { source, lit } => format!("{}: {}", source, pretty_lit(lit)),
        }
    }

    pub fn pretty_type(t: &Type) -> String {
        match t {
            Type::TVar(n) => n.clone(),
            Type::TNamed(n) => n.clone(),
            Type::TArrow(a, b) => format!("{} ~> {}", pretty_type(a), pretty_type(b)),
            Type::TProd(a, b) => format!("({} × {})", pretty_type(a), pretty_type(b)),
            Type::TSum(a, b) => format!("({} + {})", pretty_type(a), pretty_type(b)),
            Type::TRecord { fields, rest } => {
                let mut parts: Vec<String> = fields.iter().map(|(n, t)| format!("{}: {}", n, pretty_type(t))).collect();
                if let Some(r) = rest {
                    parts.push(format!("| {}", r));
                }
                format!("{{ {} }}", parts.join(", "))
            }
            Type::TTuple(items) => {
                let parts: Vec<String> = items.iter().map(pretty_type).collect();
                format!("[{}]", parts.join(", "))
            }
        }
    }
}

// ============================================================================
// Module: kernel (ADR-0052 six combinators)
// ============================================================================

pub mod kernel {
    /// The six kernel combinators from ADR-0052: arr / >>> (Seq) / first /
    /// choice / loop / app. This is the IR the desugar pass targets.
    #[derive(Debug, Clone, PartialEq)]
    pub enum Kernel {
        /// `arr f` — lift a named pure function (or library arrow) into an arrow.
        Arr { op: String, args: Vec<Kernel> },
        /// `>>>` — sequential composition.
        Seq { fst: Box<Kernel>, snd: Box<Kernel> },
        /// `first` — run inner on the first component of a product.
        First { inner: Box<Kernel> },
        /// `choice` — route on a sum: l handles Left, r handles Right.
        Choice { l: Box<Kernel>, r: Box<Kernel> },
        /// `loop` — feedback (Paterson). body: (In, State) ~> (Out, State).
        Loop { body: Box<Kernel> },
        /// `app` — dynamic/higher-order arrow application.
        App { callee: Box<Kernel>, args: Vec<Kernel> },
        /// A variable reference (resolved at a later lowering stage to env
        /// projection). Kept so the desugar output is readable.
        Var(String),
        /// A literal value lifted via `arr (const v)`.
        Const(super::ast::Lit),
        /// `ModuleRef { path }` — opaque reference to a module's arrow (resolved
        /// by a normalization strategy, ADR-0069 §5). Placeholder until a
        /// resolver inlines it.
        ModuleRef { path: String },
        /// `Project { field, record }` — project a named field from a record
        /// arrow. This is `first` + `arr` (field projection), ADR-0069 / ID.16.
        Project { field: String, record: Box<Kernel> },
        /// `Handle { body, target, impl_ }` — install a handler (ADR-0076):
        /// resolve `target` to `impl_` within `body`. This is the IR lowering
        /// of the `handle ... with` surface form.
        Handle { body: Box<Kernel>, target: String, impl_: Box<Kernel> },
    }

    impl Kernel {
        pub fn seq(a: Kernel, b: Kernel) -> Kernel {
            Kernel::Seq { fst: Box::new(a), snd: Box::new(b) }
        }
        pub fn arr(op: &str, args: Vec<Kernel>) -> Kernel {
            Kernel::Arr { op: op.to_string(), args }
        }
        pub fn project(field: &str, record: Kernel) -> Kernel {
            Kernel::Project { field: field.to_string(), record: Box::new(record) }
        }
        pub fn module_ref(path: &str) -> Kernel {
            Kernel::ModuleRef { path: path.to_string() }
        }
        /// Construct a `Handle` node: install `impl_` for `target` within `body`.
        pub fn handle(body: Kernel, target: &str, impl_: Kernel) -> Kernel {
            Kernel::Handle {
                body: Box::new(body),
                target: target.to_string(),
                impl_: Box::new(impl_),
            }
        }
    }
}

// ============================================================================
// Module: desugar
// ============================================================================

pub mod desugar {
    use super::ast::*;
    use super::kernel::Kernel;

    /// The result of desugaring a program: a list of (name, kernel) bindings
    /// plus an export set describing which names are public.
    #[derive(Debug, Clone, PartialEq)]
    pub struct DesugaredProgram {
        pub bindings: Vec<(String, Kernel)>, // name -> kernel (imports + bindings + export-bindings)
        pub export_set: ExportSet,
        /// Paths pending `export * from "path"`. The remote module's public
        /// names are not known at desugar time; a later resolver/normalizer
        /// (Subagent 3) expands each path into Project bindings and adds them
        /// to the export set. No bindings are emitted here for these.
        pub reexports: Vec<String>,
    }

    #[derive(Debug, Clone, PartialEq)]
    pub enum ExportSet {
        All,               // no export declarations: all bindings public
        Names(Vec<String>), // explicit export list
    }

    /// Desugar a program: imports become `Project` over `ModuleRef`, bindings
    /// become kernel arrows, and exports determine the public name set.
    /// See ARROW_DESUGARING_V0_1.md §12.
    pub fn desugar_program(p: &Program) -> DesugaredProgram {
        let mut bindings: Vec<(String, Kernel)> = Vec::new();
        let mut explicit_names: Vec<String> = Vec::new();
        let mut reexports: Vec<String> = Vec::new();
        let mut saw_export = false;
        let mut export_all = false;

        // Imports → Project bindings (or ModuleRef for whole-module import).
        for im in &p.imports {
            match im {
                Import::Names { specs, path } => {
                    for sp in specs {
                        bindings.push((
                            sp.local.clone(),
                            Kernel::Project {
                                field: sp.name.clone(),
                                record: Box::new(Kernel::ModuleRef { path: path.clone() }),
                            },
                        ));
                    }
                }
                Import::Whole { path, alias } => {
                    bindings.push((alias.clone(), Kernel::ModuleRef { path: path.clone() }));
                }
            }
        }

        // Plain bindings.
        for b in &p.bindings {
            bindings.push((b.name.clone(), desugar_expr(&b.value)));
        }

        // Exports.
        for ex in &p.exports {
            saw_export = true;
            match ex {
                Export::Names { names } => {
                    for n in names {
                        explicit_names.push(n.clone());
                    }
                }
                Export::Bindings { bindings: bs } => {
                    for b in bs {
                        bindings.push((b.name.clone(), desugar_expr(&b.value)));
                        explicit_names.push(b.name.clone());
                    }
                }
                Export::All => {
                    // `export *` means all bindings are public. Combined with
                    // explicit names it is still all, so this dominates.
                    export_all = true;
                }
                Export::NamesFrom { names, path } => {
                    for n in names {
                        bindings.push((
                            n.clone(),
                            Kernel::Project {
                                field: n.clone(),
                                record: Box::new(Kernel::ModuleRef { path: path.clone() }),
                            },
                        ));
                        explicit_names.push(n.clone());
                    }
                }
                Export::AllFrom { path } => {
                    // Remote public names unknown at desugar time; record the
                    // path for the resolver/normalizer to expand later.
                    reexports.push(path.clone());
                }
            }
        }

        let export_set = if !saw_export {
            ExportSet::All
        } else if export_all {
            // `export *` dominates: all bindings public.
            ExportSet::All
        } else {
            ExportSet::Names(explicit_names)
        };

        DesugaredProgram { bindings, export_set, reexports }
    }

    pub fn desugar_expr(e: &Expr) -> Kernel {
        match e {
            Expr::Var(n) => Kernel::Var(n.clone()),
            Expr::Wild => Kernel::arr("wild", vec![]),
            Expr::Lit(l) => Kernel::Const(l.clone()),
            Expr::Paren { inner } => desugar_expr(inner),
            // x ~> e  ~>  arr (λx. ⟦e⟧)  (the body lifted into arr)
            Expr::Arrow { pat, body, .. } => {
                let body_k = desugar_expr(body);
                Kernel::arr("arrow", vec![desugar_pattern(pat), body_k])
            }
            Expr::App { f, arg } => {
                // Static callee: composition (args >>> callee). We represent as
                // Seq(arg, f) — the argument feeds into the arrow f.
                Kernel::seq(desugar_expr(arg), desugar_expr(f))
            }
            Expr::Compose { l, r } => Kernel::seq(desugar_expr(l), desugar_expr(r)),
            Expr::Product { l, r } => {
                // f *** g  ~>  first-based product (ADR-0052 derived forms).
                Kernel::Arr {
                    op: "product".to_string(),
                    args: vec![desugar_expr(l), desugar_expr(r)],
                }
            }
            Expr::FanOut { l, r } => Kernel::Arr {
                op: "fanout".to_string(),
                args: vec![desugar_expr(l), desugar_expr(r)],
            },
            Expr::Choice { l, r } => Kernel::Choice { l: Box::new(desugar_expr(l)), r: Box::new(desugar_expr(r)) },
            // x + y  ~>  add [x, y]  (library arrow application, ID.8)
            Expr::BinOp { op, l, r } => {
                let op_arrow = match op.as_str() {
                    "+" => "add",
                    "-" => "sub",
                    "*" => "mul",
                    "/" => "div",
                    "==" => "eq",
                    "!=" => "neq",
                    "<" => "lt",
                    ">" => "gt",
                    "<=" => "lte",
                    ">=" => "gte",
                    "&&" => "and",
                    "||" => "or",
                    other => other,
                };
                let args = Kernel::Arr {
                    op: "tuple".to_string(),
                    args: vec![desugar_expr(l), desugar_expr(r)],
                };
                Kernel::seq(args, Kernel::Var(op_arrow.to_string()))
            }
            // a ?? b  ~>  match a { some: value, none: b, _: b }  (desugaring spec §6)
            Expr::Nullish { l, r } => Kernel::Choice {
                l: Box::new(Kernel::arr("some_extract", vec![desugar_expr(l)])),
                r: Box::new(desugar_expr(r)),
            },
            // user?.field  ~>  >>> (?.field arrow)  (desugaring spec §7)
            Expr::OptChain { src, field } => Kernel::seq(
                desugar_expr(src),
                Kernel::arr("opt_field", vec![Kernel::Const(Lit::Str(field.clone()))]),
            ),
            Expr::Field { src, name } => Kernel::seq(desugar_expr(src), Kernel::arr("field", vec![Kernel::Const(Lit::Str(name.clone()))])),
            Expr::Index { src, idx } => Kernel::seq(desugar_expr(src), Kernel::arr("index", vec![desugar_expr(idx)])),
            // Spread / record / tuple: arr merge node (desugaring spec §8)
            Expr::Record { fields } => {
                let args: Vec<Kernel> = fields
                    .iter()
                    .map(|f| match f {
                        RecordField::Named { name, value } => Kernel::arr(
                            "field",
                            vec![Kernel::Const(Lit::Str(name.clone())), desugar_expr(value)],
                        ),
                        RecordField::Shorthand { name } => Kernel::arr(
                            "field",
                            vec![Kernel::Const(Lit::Str(name.clone())), Kernel::Var(name.clone())],
                        ),
                        RecordField::Computed { key, value } => Kernel::arr(
                            "field",
                            vec![desugar_expr(key), desugar_expr(value)],
                        ),
                        RecordField::Spread { value } => Kernel::arr("spread", vec![desugar_expr(value)]),
                    })
                    .collect();
                Kernel::arr("record", args)
            }
            Expr::Tuple { items } => {
                let args: Vec<Kernel> = items.iter().map(desugar_expr).collect();
                Kernel::arr("tuple", args)
            }
            Expr::Spread { value } => Kernel::arr("spread", vec![desugar_expr(value)]),
            // if c then a else b  ~>  c >>> arr(tag) >>> choice a b
            Expr::If { cond, then, else_ } => Kernel::seq(
                Kernel::seq(desugar_expr(cond), Kernel::arr("tag", vec![])),
                Kernel::Choice { l: Box::new(desugar_expr(then)), r: Box::new(desugar_expr(else_)) },
            ),
            // multi-way if  ~>  nested if/else (desugaring spec §9)
            Expr::MultiIf { arms } => {
                // Fold right: if c1 e1 else (if c2 e2 else (... else e_catchall))
                let mut iter = arms.iter().rev();
                let catch = iter.next().expect("multi-way if has arms");
                let mut acc = if catch.catch_all {
                    desugar_expr(&catch.body)
                } else {
                    // No explicit catch-all; last arm is the fallthrough.
                    Kernel::seq(
                        Kernel::seq(desugar_expr(&catch.cond), Kernel::arr("tag", vec![])),
                        Kernel::Choice { l: Box::new(desugar_expr(&catch.body)), r: Box::new(Kernel::arr("unreachable", vec![])) },
                    )
                };
                for arm in iter {
                    let k = Kernel::seq(
                        Kernel::seq(desugar_expr(&arm.cond), Kernel::arr("tag", vec![])),
                        Kernel::Choice { l: Box::new(desugar_expr(&arm.body)), r: Box::new(acc) },
                    );
                    acc = k;
                }
                acc
            }
            // match v { p: e }  ~>  v >>> choice ... (pattern dispatch via |||)
            Expr::Match { scrutinee, arms } => {
                // Build a choice tree over the arms. This is a sketch; full
                // pattern dispatch requires sum-type routing (desugaring spec).
                let mut acc = Kernel::arr("unreachable", vec![]);
                for arm in arms.iter().rev() {
                    acc = Kernel::Choice { l: Box::new(desugar_expr(&arm.body)), r: Box::new(acc) };
                }
                Kernel::seq(desugar_expr(scrutinee), acc)
            }
            // while c { body }  ~>  rec with implicit feedback (desugaring spec §3)
            Expr::While { cond, body, .. } => Kernel::Loop {
                body: Box::new(Kernel::seq(
                    desugar_expr(cond),
                    Kernel::Choice { l: Box::new(desugar_expr(body)), r: Box::new(Kernel::arr("exit", vec![])) },
                )),
            },
            // do { body } while c  ~>  rec, body-first (desugaring spec §4)
            Expr::DoWhile { body, cond } => Kernel::Loop {
                body: Box::new(Kernel::seq(
                    desugar_expr(body),
                    Kernel::seq(
                        desugar_expr(cond),
                        Kernel::Choice { l: Box::new(Kernel::arr("feedback", vec![])), r: Box::new(Kernel::arr("exit", vec![])) },
                    ),
                )),
            },
            // for x in xs { body }  ~>  rec + Iterator.next + match (desugaring spec §5)
            // TODO: full Iterator dispatch per desugaring spec §5 (requires
            // Iterator trait, ADR-0075). Sketched here as a loop over next.
            Expr::For { var, iter, acc, body } => {
                let _ = (var, acc);
                Kernel::Loop {
                    body: Box::new(Kernel::seq(
                        Kernel::seq(desugar_expr(iter), Kernel::arr("iter_next", vec![])),
                        Kernel::Choice { l: Box::new(desugar_expr(body)), r: Box::new(Kernel::arr("exit", vec![])) },
                    )),
                }
            }
            // rec { ... }  ~>  Loop (Paterson feedback, ID.3)
            Expr::Rec { body } => Kernel::Loop { body: Box::new(desugar_expr(body)) },
            Expr::Return { value } => Kernel::arr("return", vec![desugar_expr(value)]),
            Expr::Block { bindings, trailing } => {
                // A block desugars to a sequence: each binding extends the env
                // (Seq + arr extend_env), then the trailing expr.
                let mut acc = match trailing {
                    Some(t) => desugar_expr(t),
                    None => Kernel::arr("unit", vec![]),
                };
                for b in bindings.iter().rev() {
                    acc = Kernel::seq(desugar_expr(&b.value), Kernel::seq(Kernel::arr("extend_env", vec![Kernel::Const(Lit::Str(b.name.clone()))]), acc));
                }
                acc
            }
            Expr::Infer { inner } => match inner {
                InferKind::Name(n) => Kernel::arr("infer_name", vec![Kernel::Const(Lit::Str(n.clone()))]),
                InferKind::Arrow(e) => Kernel::arr("infer_arrow", vec![desugar_expr(e)]),
            },
            // handle body with target = impl_  ~>  Kernel::Handle (ADR-0076)
            Expr::Handle { body, target, impl_ } => Kernel::handle(
                desugar_expr(body),
                target,
                desugar_expr(impl_),
            ),
            // law <name>: [forall <vars>.] <lhs> = <rhs>  (ADR-0076)
            // Laws are meta-level equations, not arrow-valued expressions.
            // They are not part of the kernel arrow IR; a later lowering pass
            // (quantified_laws) collects them into a QuantifiedLaw catalog.
            // Here we emit a placeholder `arr("law", ...)` so the desugar map
            // stays total; the real law extraction happens upstream of desugar.
            Expr::Law { name, vars, lhs, rhs } => {
                let mut args = vec![Kernel::Const(Lit::Str(name.clone()))];
                for v in vars {
                    args.push(Kernel::Const(Lit::Str(v.clone())));
                }
                args.push(desugar_expr(lhs));
                args.push(desugar_expr(rhs));
                Kernel::arr("law", args)
            }
        }
    }

    fn desugar_pattern(p: &Pattern) -> Kernel {
        match p {
            Pattern::PVar(n) => Kernel::Const(Lit::Str(n.clone())),
            Pattern::PWild => Kernel::arr("wild", vec![]),
            Pattern::PLit(l) => Kernel::Const(l.clone()),
            Pattern::PRest(n) => Kernel::arr("rest", vec![Kernel::Const(Lit::Str(n.clone()))]),
            Pattern::PRecord { elements } => {
                let args: Vec<Kernel> = elements
                    .iter()
                    .map(|e| match e {
                        PatternElement::Rename { source, local } => Kernel::arr("rename", vec![Kernel::Const(Lit::Str(source.clone())), Kernel::Const(Lit::Str(local.clone()))]),
                        PatternElement::Shorthand { name } => Kernel::arr("shorthand", vec![Kernel::Const(Lit::Str(name.clone()))]),
                        PatternElement::Nested { source, pat } => Kernel::arr("nested", vec![Kernel::Const(Lit::Str(source.clone())), desugar_pattern(pat)]),
                        PatternElement::Rest { name } => Kernel::arr("rest", vec![Kernel::Const(Lit::Str(name.clone()))]),
                        PatternElement::Lit { source, lit } => Kernel::arr("plit", vec![Kernel::Const(Lit::Str(source.clone())), Kernel::Const(lit.clone())]),
                    })
                    .collect();
                Kernel::arr("record_pat", args)
            }
            Pattern::PTuple { items } => Kernel::arr("tuple_pat", items.iter().map(desugar_pattern).collect()),
            Pattern::PConstruct { tag, args } => Kernel::arr("construct_pat", std::iter::once(Kernel::Const(Lit::Str(tag.clone()))).chain(args.iter().map(desugar_pattern)).collect()),
        }
    }
}

// ============================================================================
// Public re-exports
// ============================================================================

pub use ast::*;
pub use kernel::Kernel;
pub use lexer::{Lexer, Token};
pub use parser::Parser;

/// Parse a source string into a Program, attaching approximate line/col info.
pub fn parse(src: &str) -> Result<Program, String> {
    // Tokenize with line/col tracking (approximate: re-lex to get positions).
    let lexer = Lexer::new(src);
    let toks = lexer.clone().tokenize().map_err(|e| e.to_string())?;
    // Build parallel line/col arrays by re-walking.
    let mut lines = Vec::with_capacity(toks.len());
    let mut cols = Vec::with_capacity(toks.len());
    let mut lx = Lexer::new(src);
    for _ in 0..toks.len() {
        lines.push(lx.line);
        cols.push(lx.col);
        let _ = lx.next_token();
    }
    let mut p = Parser::new(toks, lines, cols);
    p.parse_program().map_err(|e| e.to_string())
}

/// Pretty-print a program.
pub fn pretty(p: &Program) -> String {
    pretty::pretty_program(p)
}

/// Parse a single expression (for tests).
pub fn parse_expr(src: &str) -> Result<Expr, String> {
    let lexer = Lexer::new(src);
    let toks = lexer.clone().tokenize().map_err(|e| e.to_string())?;
    let mut lines = Vec::with_capacity(toks.len());
    let mut cols = Vec::with_capacity(toks.len());
    let mut lx = Lexer::new(src);
    for _ in 0..toks.len() {
        lines.push(lx.line);
        cols.push(lx.col);
        let _ = lx.next_token();
    }
    let mut p = Parser::new(toks, lines, cols);
    p.parse_expr(0).map_err(|e| e.to_string())
}

/// Desugar a program to the kernel IR.
pub fn desugar(p: &Program) -> desugar::DesugaredProgram {
    desugar::desugar_program(p)
}

// ============================================================================
// Smoke-test main
// ============================================================================

fn main() {
    println!("handl v0.1 Surface — Reference Parser smoke test");
    println!("==================================================\n");
    let samples = [
        "x ~> x * 2",
        "greet = { name: userName } ~> userName",
        "name = user.name ?? \"anonymous\"",
        "user?.address?.city",
        "while n > 0 { n = n - 1 }",
        "for x in xs { x * 2 }",
        "for x in xs, acc = 0 { acc + x }",
        "add = [x, y] ~> x + y",
    ];
    for s in &samples {
        match parse_expr(s) {
            Ok(e) => println!("  OK  {}  =>  {}", s, pretty::pretty_expr(&e, 0)),
            Err(e) => println!("  ERR {}  =>  {}", s, e),
        }
    }

    // Module-system smoke tests (ADR-0069 "Files Are Arrows" + export sugar).
    println!("\nModule-system smoke tests:");
    let module_samples = [
        "import sort, head from \"collection\"",
        "import sort as s from \"collection/sort\"",
        "import \"collection\" as c",
        "export sort",
        "export sort = first(id) >>> insert",
        "export *",
        "export sort from \"collection/sort\"",
        "export * from \"collection\"",
    ];
    let mut all_ok = true;
    for s in &module_samples {
        match parse(s) {
            Ok(p) => {
                let pp = pretty(&p);
                match parse(&pp) {
                    Ok(p2) => {
                        if p == p2 {
                            println!("  OK  {}  =>  {}", s, pp.trim());
                        } else {
                            println!("  FAIL [round-trip] {}", s);
                            println!("       parsed:  {:?}", p);
                            println!("       printed: {}", pp);
                            println!("       re-parsed: {:?}", p2);
                            all_ok = false;
                        }
                    }
                    Err(e) => {
                        println!("  FAIL [re-parse] {}  =>  {}  (printed: {})", s, e, pp);
                        all_ok = false;
                    }
                }
            }
            Err(e) => {
                println!("  FAIL [parse] {}  =>  {}", s, e);
                all_ok = false;
            }
        }
    }
    // Desugar smoke: import sort from "collection/sort" → Project/ModuleRef.
    match parse("import sort from \"collection/sort\"") {
        Ok(p) => {
            let ds = desugar(&p);
            if let Some((n, k)) = ds.bindings.iter().find(|(n, _)| n == "sort") {
                if matches!(k, Kernel::Project { field, record } if field == "sort"
                    && matches!(record.as_ref(), Kernel::ModuleRef { path } if path == "collection/sort"))
                {
                    println!("  OK  desugar import sort  =>  {:?}", k);
                } else {
                    println!("  FAIL [desugar] import sort  =>  {:?}", k);
                    all_ok = false;
                }
            } else {
                println!("  FAIL [desugar] import sort: no binding named sort");
                all_ok = false;
            }
        }
        Err(e) => {
            println!("  FAIL [desugar parse] import sort  =>  {}", e);
            all_ok = false;
        }
    }

    // Handler smoke tests (ADR-0076 `handle ... with` surface syntax).
    println!("\nHandler smoke tests (handle ... with):");
    let handle_samples = [
        "handle sort_by intCmp list with map = map_list",
        "handle migrate json with Serializer<JSON> = json_impl",
        "handle body with Functor<List> = map_list",
        "handle run prog with Eq<Int> = intEq",
    ];
    for s in &handle_samples {
        match parse_expr(s) {
            Ok(e) => {
                let printed = pretty::pretty_expr(&e, 0);
                // Round-trip: parse the pretty-printed form, compare ASTs.
                match parse_expr(&printed) {
                    Ok(e2) => {
                        if e == e2 {
                            println!("  PASS [round-trip] {}  =>  {}", s, printed);
                        } else {
                            println!("  FAIL [round-trip] {}", s);
                            println!("       parsed:  {:?}", e);
                            println!("       printed: {}", printed);
                            println!("       re-parsed: {:?}", e2);
                            all_ok = false;
                        }
                    }
                    Err(e) => {
                        println!("  FAIL [re-parse] {}  =>  {}  (printed: {})", s, e, printed);
                        all_ok = false;
                    }
                }
            }
            Err(e) => {
                println!("  FAIL [parse] {}  =>  {}", s, e);
                all_ok = false;
            }
        }
    }

    // Handler AST shape: parse produces Expr::Handle with the right fields.
    match parse_expr("handle sort_by intCmp list with map = map_list") {
        Ok(e) => match e {
            Expr::Handle { body, target, impl_ } => {
                if target == "map"
                    && matches!(body.as_ref(), Expr::App { .. })
                    && matches!(impl_.as_ref(), Expr::Var(ref n) if n == "map_list")
                {
                    println!("  PASS [ast] handle sort_by intCmp list with map = map_list  =>  Handle {{ target: {} }}", target);
                } else {
                    println!("  FAIL [ast] handle: wrong fields  target={:?} body={:?} impl_={:?}", target, body, impl_);
                    all_ok = false;
                }
            }
            other => {
                println!("  FAIL [ast] expected Expr::Handle, got {:?}", other);
                all_ok = false;
            }
        },
        Err(e) => {
            println!("  FAIL [ast parse] handle  =>  {}", e);
            all_ok = false;
        }
    }

    // Handler with type args: target captures `Serializer<JSON>`.
    match parse_expr("handle migrate json with Serializer<JSON> = json_impl") {
        Ok(e) => match e {
            Expr::Handle { target, .. } if target == "Serializer<JSON>" => {
                println!("  PASS [type-args] target = {}", target);
            }
            Expr::Handle { target, .. } => {
                println!("  FAIL [type-args] expected Serializer<JSON>, got {}", target);
                all_ok = false;
            }
            other => {
                println!("  FAIL [type-args] expected Expr::Handle, got {:?}", other);
                all_ok = false;
            }
        },
        Err(e) => {
            println!("  FAIL [type-args parse]  =>  {}", e);
            all_ok = false;
        }
    }

    // Desugar: Expr::Handle -> Kernel::Handle.
    match parse_expr("handle body with map = map_list") {
        Ok(e) => {
            let k = desugar::desugar_expr(&e);
            let is_handle = matches!(
                k,
                Kernel::Handle { ref target, .. } if target == "map"
            );
            if is_handle {
                println!("  PASS [desugar] handle body with map = map_list  =>  {:?}", k);
            } else {
                println!("  FAIL [desugar] expected Kernel::Handle with target map, got {:?}", k);
                all_ok = false;
            }
        }
        Err(e) => {
            println!("  FAIL [desugar parse]  =>  {}", e);
            all_ok = false;
        }
    }

    // Parse-error cases: `handle` without `with`, and `with` without `=`.
    match parse_expr("handle sort_by intCmp list") {
        Ok(e) => {
            println!("  FAIL [error] handle-without-with should fail, got: {:?}", e);
            all_ok = false;
        }
        Err(e) => {
            println!("  PASS [error] handle-without-with  =>  {}", e);
        }
    }
    match parse_expr("handle body with map map_list") {
        Ok(e) => {
            println!("  FAIL [error] with-without-eq should fail, got: {:?}", e);
            all_ok = false;
        }
        Err(e) => {
            println!("  PASS [error] with-without-eq  =>  {}", e);
        }
    }

    if !all_ok {
        println!("\nSmoke test FAILED.");
        std::process::exit(1);
    }
    println!("\n(See v0_1_surface_tests for the full test suite.)");
}

// ============================================================================
// Limitations
// ============================================================================
//
// This is a *reference* parser, not the production parser. Known limitations
// (documented for the v0.1 implementer):
//
// 1. **Optional punctuation.** Newlines are treated as whitespace. Separators
//    (`,` / `;`) are required between match arms, multi-way `if` arms, and
//    tuple elements. Records and blocks use lookahead (no separator needed).
//    The production parser (ADR-0053) tracks newlines for full optional-
//    punctuation support; this reference parser accepts the canonical comma-
//    separated form.
// 2. **Sum-type constructor patterns** (`some x`, `Left y`) are parsed as
//    `PConstruct` via application-in-pattern-position, but exhaustiveness
//    checking (ID.13) is not implemented (it is a typechecker concern).
// 3. **`for` desugaring** is sketched (TODO: full Iterator dispatch per
//    desugaring spec §5, requires ADR-0075).
// 4. **Type annotations** are parsed minimally (no row-variable unification,
//    no `infer` typing rule — those are ADR-0054 concerns).
// 5. **`type.Name` namespace** in types is recognized (`type.Int` → TNamed
//    "Int"); the `type` keyword in other positions is not special.
//
// The core surface forms (arrows, composition, destructuring with renaming,
// if/match, while/do-while/for, rec, ??, ?., spread, multi-arg, import) parse
// and pretty-print with round-trip fidelity, and desugar to the kernel IR
// (ADR-0052). This is sufficient as a reference for the v0.1 implementer.
