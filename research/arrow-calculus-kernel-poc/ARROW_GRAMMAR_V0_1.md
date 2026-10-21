# Arrow Language v0.1 Surface Grammar

## Status

Authoritative — v0.1 surface grammar per ADR-0074 follow-up #1. Implements the
syntax of `ARROW_LANGUAGE_SPEC_V0_1.md` against the
[ADR-0053 — Generic Pratt Parser](../../project/adrs/0053-generic-pratt-parser.md)
data-driven Pratt model.

This document is the **parser-ready formal grammar** for the handl v0.1 surface
syntax. It turns the syntax section of the Arrow Language Specification v0.1
into a specification precise enough that an implementer can build a Pratt parser
directly from it. Every construct in the spec is given a grammar rule, and every
construct that fits ADR-0053's prefix/infix + delimited-block model is mapped to
an explicit grammar row. Where a construct falls outside ADR-0053's expressiveness
(per ADR-0053 §"Scope boundary"), this document says so honestly and identifies
the required special-case or schema extension.

The surface syntax denotes the six-combinator kernel of
[ADR-0052 — Arrow Calculus Kernel](../../project/adrs/0052-arrow-calculus-kernel.md)
(`arr` / `>>>` / `first` / `choice` / `loop` / `app`). The module model is
[ADR-0069 — Files Are Arrows](../../project/adrs/0069-arrow-native-modules.md);
the decision of record is
[ADR-0074 — Arrow Surface Syntax v0.1 — Redesign](../../project/adrs/0074-arrow-syntax-v0_1-surface-redesign.md).

---

## 1. Notation & Conventions

### 1.1 Grammar notation

This document uses BNF-style productions in ```text fences. The conventions are:

- **Nonterminals** are written in lowercase angle-free form, e.g. `expr`,
  `pattern`, `record_literal`. A nonterminal appears on the left of `::=`.
- **Terminals** are written in single quotes for literal tokens (`'~>'`,
  `'{'`, `'true'`) or named in `token.*` form when referring to a token _kind_
  (per ADR-0053's `token.kind` naming), e.g. `token.lbrace`, `token.keyword.if`.
- **Repetition** is denoted by `( ... )*` (zero or more) and `( ... )+` (one or
  more). **Optionality** is denoted by `( ... )?`.
- **Alternation** is denoted by `|`.
- The meta-symbols `::=`, `|`, `(`, `)`, `*`, `+`, `?` are part of the notation,
  not the language. Where a literal `(`, `)`, `*`, `+`, or `?` is a terminal of
  the language, it is quoted.
- `NEWLINE` denotes a significant newline (a statement/binding separator, see
  §2.3). `;` is an equivalent explicit separator.

### 1.2 Relationship to ADR-0053

The grammar is designed to be consumed by ADR-0053's **data-driven Pratt
parser**. ADR-0053 parses expressions by consulting grammar rows keyed by
`(token_kind, position)` where `position ∈ {Prefix, Infix}`. Each row carries:

- a **binding power** pair `(lbp, rbp_right)` for infix rows (the prefix path
  uses a single `prefix_rbp` for the recursive call);
- a **child shape**: `arity`, optional `child_separators: Vec<ChildSeparator>`,
  and an optional `DelimitedShape` for the trailing delimited block;
- a `node_kind` (the AST node kind produced);
- an optional `desugar: DesugarRule` (a post-parse rewrite, ADR-0053 §7).

The prefix/infix loop (ADR-0053 §"Resulting `expression_inner`") is:

```text
prefix:
  token = advance
  row = lookup(token, Prefix) or error
  shape = row.child_shape
  if shape.arity == 0:
    push atom_payload(token)            -- dispatches on LiteralKind
  else:
    normal = shape.arity - (shape.delimited ? 1 : 0)
    children = []
    for i in 0..normal:
      children.push(expression(row.prefix_rbp))
      if i < normal - 1: consume(shape.child_separators[i])
    if shape.delimited:
      children.push(parse_delimited_block(shape.delimited))
    push node(shape.node_kind, children)

infix:
  row = lookup(token, Infix) or break
  (lbp, rbp_right) = row.binding_power
  if lbp < rbp: break                    -- rbp is the left operand's continuation
  advance operator
  shape = row.child_shape
  normal = shape.arity - 1 - (shape.delimited ? 1 : 0)
  children = [left]
  for i in 0..normal:
    children.push(expression(rbp_right))
    if i < normal - 1: consume(shape.child_separators[i])
  if shape.delimited:
    if shape.delimited.flatten: children.extend(parse_delimited_block(...).elements)
    else: children.push(parse_delimited_block(...))
  push node(shape.node_kind, children)
```

`DelimitedShape` carries `open`, `close`, `separator`, `pair` (for key/value
entries), `rest_token` (for spread), `open_is_operator_token`, `flatten`, and
`container_kind`. `LiteralKind` discriminates literal interpretation
(`Number`, `Bool`, `String`, `Raw`, ...). These terms are used throughout §5.

### 1.3 The contextual `{}` rule (ID.11)

The grammar has exactly **one context-sensitive rule**: the disambiguation of
`{` as beginning a **block** versus a **record**. This is accepted as a
contextual (position-based) rule because the alternative — distinct delimiters
for records and blocks — was rejected as syntactic noise in an
expression-oriented language (ADR-0074 Negative, spec §7.5).

**Decision procedure.** A `{` token begins a **block** when the parser is in
one of the following _block-expecting contexts_ (i.e. the `{` immediately
follows one of these constructs, with at most the construct's own trailing
operands already consumed):

1. immediately after a `~>` (the arrow body is a block): `pattern ~> { ... }`;
2. immediately after the condition of a two-branch `if`: `if cond { ... }`;
3. immediately after `else`: `... else { ... }`;
4. immediately after the scrutinee of a `match`: `match val { ... }` — here the
   outer `{}` is the **match body** (block-like, holding pattern arms);
5. immediately after the condition of a `while`: `while cond { ... }`;
6. immediately after the header of a `for`: `for x in xs { ... }` or
   `for x in xs, acc = init { ... }`;
7. immediately after `rec`: `rec { ... }`;
8. immediately after `do`: `do { ... } while cond`.

In **all other positions** a `{` begins a **record** — specifically, in
_value position_ (an expression operand) and in _pattern position_ (the LHS of
`~>`, a `match` arm pattern, a destructuring binding LHS). The one subtlety:
inside `match val { ... }`, the outer `{}` is the match body (block-like,
holding arms); any `{}` that appears _inside a pattern position_ within an arm
is a **record pattern** (§9, §10), not a block. That is, the arm grammar is
`pattern : expr`, and the `pattern` nonterminal may itself contain
`record_pattern` / `positional_pattern` delimited by `{}` / `[]`, which are
records/positional structures, not blocks.

This rule is implemented by the parser tracking a one-bit "block-expecting"
context flag, set when consuming the constructs above and cleared when entering
a value or pattern operand. It is not expressible as a context-free production;
it is the single acknowledged context-sensitivity of the v0.1 surface.

---

## 2. Lexical Grammar

### 2.1 Identifiers

```text
identifier      ::= identifier_start identifier_continue*
identifier_start  ::= [a-zA-Z_]
identifier_continue ::= [a-zA-Z0-9_']
```

Identifiers are case-sensitive. Wire and arrow names are lowercase by
convention (`parse`, `greet`, `add`). Type names referenced via the `type.`
namespace use the library's casing (`type.Str`, `type.Int`). Sum tags are
lowercase (§14, ID.4). An identifier that coincides with a keyword (§2.5) is a
parse error (spec §2.6).

### 2.2 Literals

Literals are **language-level** (ID.8): the parser produces them directly via
`LiteralKind` dispatch (ADR-0053 §1). Operations _on_ literals are library
arrows, not language primitives.

```text
literal        ::= 'true' | 'false'        -- booleans (lowercase)
                | integer_literal
                | float_literal
                | string_literal

integer_literal ::= [0-9]+
float_literal   ::= [0-9]+ '.' [0-9]+
string_literal  ::= '"' (string_char | escape)* '"'
escape          ::= '\\' ('n' | 't' | '"' | '\\' | ...)
```

- **Booleans** are `true` and `false` (lowercase). There is no `True`/`False`.
- **Numbers** are integer or floating-point: `1`, `1.5`, `42`. The numeric
  type is inferred or annotated via the `type.` namespace (`type.Int`,
  `type.Float`).
- **Strings** are double-quoted: `"hello"`. The escape table is data-driven
  per ADR-0053 `LiteralKind::String { delim_chars, escapes }`.

### 2.3 Comments, whitespace, and newline significance

```text
comment       ::= '--' [^\n]*          -- line comment to end of line
```

Only `--` line comments are specified in v0.1 (spec §2.3). There are **no
block comments**.

**Whitespace** (spaces, tabs, carriage returns) is insignificant except as it
separates tokens. **Newlines** are significant in exactly one role: as a
**statement/binding separator**. A newline (or an explicit `;`) separates
consecutive bindings in a `block`, `program`, or `rec` region, and consecutive
arms/fields/elements may also be newline-separated where commas are optional
(§4). Otherwise a newline is whitespace.

The lexer emits a `token.newline` token only in separator-significant
contexts; equivalently, the parser treats a run of one or more newlines as a
single optional separator where the grammar permits `NEWLINE` or `;`. This
keeps the grammar context-free at the phrase level while honoring the
"optional punctuation" design principle (spec §1.10, ADR-0074).

### 2.4 Token kinds

The token kinds recognized by the lexer (referenced by `token.*` names below,
per ADR-0053's naming convention):

```text
-- Identifiers / literals
token.identifier
token.keyword.if        token.keyword.else     token.keyword.match
token.keyword.rec       token.keyword.while   token.keyword.do
token.keyword.for      token.keyword.in       token.keyword.return
token.keyword.import   token.keyword.from     token.keyword.infer
token.keyword.export   token.keyword.as
token.keyword.type     token.keyword.trait    token.keyword.impl
token.keyword.law
token.literal.true     token.literal.false
token.literal.integer  token.literal.float   token.literal.string
token.wildcard                          -- '_'

-- Combinators and sugar
token.arrow          -- '~>'
token.seq            -- '>>>'
token.product        -- '***'
token.keyword.fanout -- '&&&'   (reserved-word spelling; see note)
token.choice         -- '|||'
token.nullish        -- '??'
token.optchain       -- '?.'
token.assign         -- '='
token.colon          -- ':'
token.comma          -- ','
token.semicolon      -- ';'
token.dot            -- '.'
token.lbracket       -- '['
token.rbracket       -- ']'
token.lbrace         -- '{'
token.rbrace         -- '}'
token.lparen         -- '('
token.rparen         -- ')'
token.ellipsis       -- '...'
token.pipe           -- '|'   -- row variables in types (§13.6)
token.newline        -- significant newline separator

-- Library operator characters (recognized by the lexer, desugared to
-- arrow application per ID.8; the parser treats these as infix/prefix
-- operator tokens at the arithmetic precedence level, §3)
token.op.plus token.op.minus token.op.star token.op.slash
token.op.eq token.op.neq token.op.lt token.op.gt
token.op.le token.op.ge token.op.and token.op.or token.op.not
```

> **Note on `&&&`.** The spec lists `&&&` among the operator characters (§2.4)
> and as the fan-out combinator (§5.1). It is treated as a reserved
> multi-character operator token. The `token.keyword.fanout` spelling above is
> illustrative of ADR-0053's `token.*` naming; an implementation may name it
> `token.fanout` or `token.ampampamp` — the name is data, only the lexeme
> `&&&` and its grammar row are normative.

### 2.5 Keywords

The reserved keywords (spec §2.5), unavailable as wire or arrow names:

```text
if  else  match  rec  while  do  for  in  return
import  from  export  as  infer  type  trait  impl  law
```

`true`, `false`, and `_` are also reserved (`_` is the wildcard/placeholder,
§13.4, ID.10). The contextual keywords (`type`, `trait`, `impl`, `law`,
`infer`) are reserved globally in v0.1 to avoid ambiguity (spec §2.6). `export`
and `as` are reserved globally in v0.1, like `import` and `from` (spec §2.5).

---

## 3. Precedence and Associativity (ID.1)

### 3.1 Precedence table (verbatim from ID.1)

From highest to lowest (spec §6, ADR-0074 ID.1):

```text
field access / indexing          (highest, left-assoc)
application (juxtaposition)      (left-assoc)
* / +  (arithmetic, library)     (left-assoc)
?? / ?.  (option sugar)          (left-assoc)
*** / &&&  (product / fan-out)   (left-assoc)
>>>  (sequential composition)    (left-assoc)
|||  (choice)                    (left-assoc)
~>  (arrow construction)         (right-assoc, lowest)
```

Explanatory notes (ID.1):

- **Application binds tighter than `>>>`:** `f x >>> g` parses as
  `(f x) >>> g`.
- **Arithmetic binds tighter than composition:** `x + 1 >>> f` parses as
  `(x + 1) >>> f`.
- **`~>` is the lowest-precedence operator and is right-associative:** the
  body of an arrow extends as far right as possible.

### 3.2 Binding-power table for the Pratt parser

The Pratt parser (ADR-0053) decides whether to continue parsing an infix
operator by comparing the operator's **left-binding-power** `lbp` against the
**right-binding-power** `rbp` carried from the caller (the left operand's
continuation threshold). For an infix operator `op` with operands parsed at
`rbp_right`:

- **left-associative** operators satisfy `lbp > rbp_right` (so a following
  same-precedence operator does _not_ continue into the right operand — it
  binds to the left result instead). Concretely, `lbp = rbp_right + 1`.
- **right-associative** operators satisfy `lbp < rbp_right` (so a following
  same-precedence operator _does_ continue into the right operand). Concretely,
  `lbp = rbp_right - 1`.

The table below assigns monotonically decreasing binding powers to the eight
levels, with a gap of 10 between levels to leave room for future operators.
`lbp` is the operator's left-binding-power; `rbp_right` is the right-binding
power used for the recursive parse of the right operand. Higher number =
tighter binding.

```text
Level  Operators                 lbp   rbp_right  Assoc    Row kind
----   ------------------------  ----  ---------  ------   ----------------------
  8    . (field)  [] (index)      90      89      left     infix (postfix)
  7    application (juxtaposition)80      79      left     infix (see §5)
  6    * / + -  (arithmetic)      70      69      left     infix
  5    ??  (and ?.)               60      59      left     infix / postfix
  4    ***  &&&                   50      49      left     infix
  3    >>>                        40      39      left     infix
  2    |||                        30      29      left     infix
  1    ~>                         20      21      right    infix (LHS is pattern)
```

Notes:

- **`~>` is right-associative** (`lbp=20 < rbp_right=21`), so `a ~> b ~> c`
  parses as `a ~> (b ~> c)`. It is also the lowest-precedence infix operator,
  so the body of an arrow extends as far right as possible (ID.1).
- **All other infix operators are left-associative** (`lbp = rbp_right + 1`).
- **`?.`** is a postfix field-access-like operator (§12.6). It shares the
  option-sugar level with `??`; as a postfix it has `lbp=60` and no right
  operand. As an infix `??` it has `lbp=60, rbp_right=59`.
- **Application (juxtaposition)** has no explicit operator token; it is
  triggered when an operand-position token (identifier, literal, `(`, `[`, `{`
  in record position, a keyword prefix form, etc.) appears where an infix
  operator could continue. ADR-0053 models this as an infix row keyed by the
  _following_ operand's leading token, with `lbp=80, rbp_right=79` and
  `node_kind: call` (see §5). This is the standard Pratt "juxtaposition as
  high-precedence infix" technique.
- **Field access `.name`** and **indexing `[expr]`** are postfix infix rows:
  `. ` is an infix row with `lbp=90` and a single identifier operand;
  `[` is an infix row with `lbp=90` and a `DelimitedShape` (close `]`,
  `flatten: true`) for the index expression.
- **Arithmetic operators** (`+ - * /` and the comparison/logical library
  operators `== != < > <= >= && ||`) are all library arrows (ID.8) parsed at
  the single arithmetic level 6, left-associative. The parser recognizes their
  tokens and emits `app`-desugared nodes; the library resolves the named arrow
  (`add`, `mul`, `eq`, ...). Multiplicative (`* /`) and additive (`+ -`) share
  the level in v0.1 (ID.1 lists them as one level); a future refinement may
  split them, which the gap (10) accommodates.
- **Prefix operator forms** (`* 2`, `+ 1`, `.name`, `??`, etc.) are point-free
  arrows (ID.8): a binary operator in prefix position desugars to
  `x ~> x <op> rhs`. These are prefix rows at `prefix_rbp` equal to their
  infix `lbp`, producing an `arr` node (§5).

---

## 4. Phrase Grammar

This section gives the full BNF for the v0.1 surface. It covers every construct
in the spec (§§1–17). Nonterminals are introduced in dependency order where
possible. The grammar is layered: `expr` is the precedence-dispatched
nonterminal; below it are the operator-level nonterminals, then the
atom/primary forms.

### 4.1 Program structure (spec §3)

```text
program  ::= (import | export | binding)* sep?
           | import* expr
sep      ::= NEWLINE | ';'

import   ::= 'import' import_spec (',' import_spec)* 'from' string_literal
             | 'import' string_literal 'as' identifier
import_spec ::= identifier ('as' identifier)?

export   ::= 'export' export_spec
             | 'export' '*' ('from' string_literal)?
             | 'export' export_spec (',' export_spec)* 'from' string_literal
export_spec ::= identifier ('=' expr)?
```

A file is an arrow (ADR-0069, spec §3.2). A **multi-binding file** desugars to a
record literal of the named arrows; a **single-expression file** is that
expression's arrow. Imports normalize to projections (ID.16, spec §3.3).
`sep` is a statement/binding separator (newline or `;`); trailing separators
are optional.

Imports are top-level only and conventionally appear before bindings (the
`import* expr` and leading-import forms). Exports are top-level and may appear
anywhere among bindings — they are opt-in visibility sugar (spec §3.4), not
sequential statements. A file with no `export` declarations exposes all named
bindings as public (the arrow-native default, ADR-0069 §6); a file with any
`export` declaration exposes only the exported names, and non-exported bindings
are private helpers.

> The spec §3.3 shows `import sort, head from "collection"` (multi-name from
> one module). The grammar above includes it, plus `import name as local from
"path"` (rename) and `import "path" as alias` (bind the whole module record).
> A single-name import `import name from "path"` is the common case; the
> multi-name form is the general form. The `export` production (spec §3.4)
> adds opt-in visibility: `export name`, `export name = expr`, `export *`, and
> re-exports `export name from "path"` / `export * from "path"`. ADR-0069 §6
> originally specified no `export` in v0.1; `export` is now added as opt-in
> visibility sugar, which the ADR explicitly permits as a future sugar
> addition.

### 4.2 Bindings (spec §3.1)

```text
binding       ::= identifier ':' type_expr '=' expr
                | identifier '=' expr
                | pattern '=' expr                 -- destructuring binding
                | identifier ',' identifier (',' identifier)* '=' expr
                                                    -- simultaneous assignment
```

A binding introduces a named wire whose value is the expression's result
(spec §3.1). Annotated bindings carry an explicit `name : Type` (spec §13.1,
ID.12). Destructuring bindings use a `pattern` on the LHS (§10.1).
Simultaneous assignment `a, b = b, c` is a destructuring binding whose LHS is
a positional pattern and whose RHS is a positional literal (spec §10.1).

> **Surface binding vs kernel `bind`.** The v0.1 surface `name = expr` is a
> **graph-block wire**, not the kernel `bind` combinator of ADR-0052. Per
> ADR-0053 §2, the surface `=` in a _block_ context desugars to `Seq` plus an
> environment extension (the kernel `bind` shape, arity 3: left, value, body)
> only when used in the `x = y in body` kernel form. The block-level surface
> binding is a named wire in a graph block; the block as a whole desugars to
> a sequence of `Seq`/env-extension nodes whose final wire is the block's
> value (spec §7.1–§7.2). See §5 for the row mapping.

### 4.3 Expressions — precedence dispatch (spec §6)

`expr` is the top expression nonterminal. The Pratt parser dispatches by
binding power; the BNF below is the equivalent layered grammar, with the
lowest-precedence operator outermost.

```text
expr        ::= arrow
arrow       ::= pattern '~>' arrow_body              -- right-assoc, lowest
              | composition
arrow_body  ::= block
              | expr

composition ::= choice
choice      ::= choice '|||' composition              -- left-assoc
              | seq
seq         ::= seq '>>>' choice                      -- left-assoc
              | product
product     ::= product '***' seq                     -- left-assoc
              | product '&&&' seq                     -- left-assoc
              | nullish
nullish     ::= nullish '??' product                  -- left-assoc
              | optchain
optchain    ::= optchain '?.' identifier              -- postfix, left-assoc
              | arithmetic
arithmetic  ::= arithmetic arith_op arithmetic        -- left-assoc, library
              | application
arith_op    ::= '+' | '-' | '*' | '/' | '==' | '!=' | '<' | '>' | '<=' | '>='
              | '&&' | '||'
application ::= application atom                       -- juxtaposition, left-assoc
              | postfix
postfix     ::= postfix '.' identifier                -- field access
              | postfix '[' expr ']'                  -- indexing
              | atom

atom        ::= literal
              | identifier
              | '_'                                   -- only in infer / patterns (ID.10)
              | '(' expr ')'
              | record_literal
              | positional_literal
              | match_expr
              | if_expr
              | while_expr
              | do_while_expr
              | for_expr
              | rec_expr
              | return_expr
              | infer_expr
              | type_expr
              | prefix_op                             -- point-free prefix operator
prefix_op   ::= arith_op atom                          -- e.g. '* 2', '+ 1'
              | '.' identifier                        -- point-free field access
```

Because `~>` is lowest-precedence and right-associative, `expr` and `arrow`
coincide at the top: every expression is potentially an arrow whose LHS is a
pattern. The Pratt parser handles this by giving `~>` `lbp=20, rbp_right=21`
(§3.2); the BNF makes the pattern-position LHS explicit (§4.4).

### 4.4 Arrow construction (spec §4)

```text
arrow       ::= pattern '~>' arrow_body
              | expr                                  -- non-arrow expressions
arrow_lhs   ::= pattern                               -- the LHS of ~> is a pattern
arrow_body  ::= block                                 -- contextual {} => block (ID.11)
              | expr
```

The LHS of `~>` is parsed in **pattern position**, not as a full `expr`
(spec §4.1, ID.1). This is the `arrow_lhs` / pattern position: a variable, a
destructuring pattern, or a positional structure (§9.2). The RHS (`arrow_body`)
is either a block (when `{` follows in block-expecting context, ID.11) or an
expression parsed at `rbp_right=21` (right-associative, so the body extends
rightward).

Point-free arrows omit the LHS and rely on the prefix rule (spec §4.3, ID.8):
`* 2`, `+ 1`, `.name` are shorthand for `x ~> x * 2`, `x ~> x + 1`,
`x ~> x.name`.

### 4.5 Composition operators (spec §5)

```text
composition ::= choice
choice      ::= choice '|||' composition
              | seq
seq         ::= seq '>>>' choice
              | product
product     ::= product '***' seq
              | product '&&&' seq
              | nullish
```

All four are infix, left-associative, at the binding powers in §3.2. `>>>` is
sequential composition; `***` is product (parallel); `&&&` is fan-out;
`|||` is choice (spec §5.1). Arrow kind signatures for `***`/`&&&`/`|||` at
the type level are not fixed in v0.1 (spec §5.3, follow-up #3).

### 4.6 Application (spec §4.2)

```text
application ::= application atom
              | postfix
```

Application is **juxtaposition** — writing an arrow next to its argument
applies it (spec §4.2). There is no parenthesized call syntax for arrow
application. Multi-arg arrows use an explicit positional structure (ID.2):
`add [a, b]`, never `add a b`. Application is left-associative and binds
tighter than `>>>` (ID.1).

### 4.7 Arithmetic (spec §14.2, ID.8)

```text
arithmetic  ::= arithmetic arith_op arithmetic
              | application
arith_op    ::= '+' | '-' | '*' | '/' | '==' | '!=' | '<' | '>'
              | '<=' | '>=' | '&&' | '||'
```

All arithmetic, comparison, and logical operators are **library arrows**
(ID.8). The parser recognizes the operator characters and desugars the
expression to arrow application: `x + y` desugars to `add [x, y]` (or the
library's named arrow). They are infix, left-associative, at level 6 (§3.2).
Prefix forms (`* 2`, `+ 1`) are point-free arrows (§4.3).

### 4.8 Option sugar (spec §12.5, §12.6, Addendum A.3, A.4)

```text
nullish     ::= nullish '??' product                   -- infix, left-assoc
              | optchain
optchain    ::= optchain '?.' identifier               -- postfix, left-assoc
              | arithmetic
```

`a ?? b` desugars to `match a { some: value, none: b, _: b }` (A.3). `?.field`
is a postfix arrow: `user?.address?.city` =
`user ~> (?.address >>> ?.city)` (A.4). Both are at level 5 (§3.2). `??` is
infix (two operands); `?.` is postfix (one operand, the field name).

### 4.9 Postfix — field access and indexing (spec §11.2)

```text
postfix     ::= postfix '.' identifier                -- field access (static key)
              | postfix '[' expr ']'                  -- indexing (dynamic key)
              | atom
```

Field access `obj.field` and indexing `obj[val]` are the highest-precedence
operators (§6, level 8). Both are postfix / infix rows (§5).

### 4.10 Records and positional literals (spec §11)

```text
record_literal     ::= '{' record_field (sep? record_field)* sep? '}'
                     | '{' '}'                          -- empty record
record_field       ::= identifier ':' expr             -- named field
                      | identifier                     -- shorthand: name => name: name
                      | '[' expr ']' ':' expr          -- computed key
                      | '...' expr                     -- spread (A.5)

positional_literal ::= '[' expr (sep? expr)* sep? ']'
                     | '[' ']'                         -- empty positional
                     | '[' '...' expr (sep? expr)* ']' -- spread in positional
                     | '[' expr (sep? expr)* sep? '...' expr ']'
```

`sep` here is `,` or `NEWLINE` (commas are optional, spec §11.1). Record
fields are `name : expr`, shorthand `name` (= `name : name`), computed key
`[key] : expr`, or spread `...expr` (A.5). Positional literals are
`[e1, e2, ...]` with optional spread `...expr` (A.5). These are prefix rows
with `DelimitedShape` (`open_is_operator_token: true`, `rest_token:
token.ellipsis`) per §5.

### 4.11 Patterns (spec §9, §10)

```text
pattern            ::= literal
                     | identifier
                     | '_'
                     | positional_pattern
                     | record_pattern
                     | nested_pattern

positional_pattern ::= '[' pattern_element (sep? pattern_element)* sep? ']'
record_pattern     ::= '{' record_pattern_element (sep? record_pattern_element)* sep? '}'
                     | '{' '}'
record_pattern_element ::= pattern_element
nested_pattern     ::= positional_pattern
                     | record_pattern
```

Pattern kinds (spec §9.2): literal, variable, `_` wildcard, positional,
record, nested.

### 4.12 The `pattern_element` grammar (spec §10.3, Correction 1)

```text
pattern_element    ::= source ':' local               -- renaming (Correction 1)
                     | identifier                     -- single-identifier shorthand
                     | '...' identifier               -- rest
                     | literal                        -- match context only
                     | nested_pattern                 -- nested positional/record

source             ::= identifier                     -- record field name
                     | integer_literal                -- positional index (if supported)
local              ::= identifier
```

- `source : local` — bind source field/position `source` to local wire `local`
  (Correction 1). For records, `source` is the field name; for positional
  structures there is no source name to rename, so the single-identifier form
  is used (spec §10.2).
- `identifier` — the single-identifier form: the identifier serves as **both
  source and local name** (the common case, preserved for brevity).
- `... identifier` — rest: capture the tail under `identifier`.
- `literal` — match a literal value (in `match` contexts only).
- `nested_pattern` — a nested positional/record pattern.

Nonsense such as `1 : x` outside match contexts is forbidden (ADR-0074
Negative, spec §10.3).

### 4.13 Match (spec §9)

```text
match_expr    ::= 'match' expr match_body
match_body     ::= '{' match_arm (sep? match_arm)* sep? '}'   -- contextual {} => block (ID.11)
match_arm      ::= pattern ':' expr
                 | '_' ':' expr                              -- wildcard catch-all
```

The outer `{}` of `match val { ... }` is the **match body** (block-like, per
ID.11); arms are `pattern : expr` with `:` separator (ADR-0074). Commas between
arms are optional (newline-separated). The `_` arm is the catch-all.
Exhaustiveness is required (ID.13). Any `{}` inside a _pattern position_ of an
arm is a record pattern, not a block (§1.3).

### 4.14 Conditionals — `if` / `else` and multi-way `if` (spec §8)

```text
if_expr       ::= two_branch_if
                | multi_way_if

two_branch_if ::= 'if' expr then_branch else_branch
then_branch   ::= block                              -- contextual {} => block (ID.11)
                | expr
else_branch   ::= 'else' block
                | 'else' expr
                | 'else' if_expr                     -- else-if chain

multi_way_if  ::= 'if' '{' guard_arm (sep? guard_arm)* sep? '}'  -- A.7
guard_arm     ::= expr ':' expr                      -- condition : result
                | '_' ':' expr                       -- catch-all
```

**Two-branch `if`** (spec §8.1): `if cond then else else_expr`, with
single-statement or braced forms. `if` is an expression producing a value.

**Multi-way `if`** (Addendum A.7): `if { c1: e1, c2: e2, _: e3 }`. Each arm is a
condition expression followed by `:` and a result. The `_` arm is the
catch-all. It mirrors `match` syntax (same `{}`, same `:`, same `_`) but each
arm is a guard condition, not a pattern. Exhaustiveness is required (ID.13).
Multi-way `if` desugars to nested `if`/`else` (A.7).

**Disambiguation (two-branch vs multi-way).** The parser inspects the token
immediately after `if`:

- If it is `{`, the form is **multi-way** (the `{` is the guard-arm block; per
  A.7 the parser distinguishes by this token). The block is parsed as a
  delimited list of `guard_arm` pairs (`expr : expr`).
- Otherwise (an expression-leading token), the form is **two-branch**. The
  parser parses the condition `expr`, then the then-branch (a block if `{`
  follows, else an expression), then requires `else` and the else-branch.

The `:` after the condition is _not_ a disambiguator in the two-branch form
because the condition is a full `expr` and `:` is not an infix operator at the
expression level (it only appears in record fields, patterns, match arms, and
guard arms). The presence of `{` immediately after `if` is the sole
disambiguator, matching A.7's stated rule.

### 4.15 `while` (spec §12.2, Addendum A.1)

```text
while_expr    ::= 'while' expr while_body
while_body    ::= block                              -- contextual {} => block (ID.11)
                | expr                               -- no-block form (A.1)
```

`while cond { body }` desugars to a `rec` region with implicit feedback (A.1).
A no-block form `while cond body` is also permitted. The result is the last
expression in the body, evaluated on the final iteration (ID.5).

### 4.16 `do { ... } while` (spec §12.4, Addendum A.6)

```text
do_while_expr ::= 'do' block 'while' expr            -- body-first, post-test
```

The body executes before the first condition check (runs at least once).
`do { body } while cond` desugars to a `rec` region that runs the body first,
then branches on the condition (A.6). The `{` after `do` is a block (ID.11).

### 4.17 `for` (spec §12.3, Addendum A.2)

```text
for_expr      ::= 'for' identifier 'in' expr for_body                -- map
                | 'for' identifier 'in' expr ',' identifier '=' expr for_body  -- fold
for_body      ::= block                              -- contextual {} => block (ID.11)
```

The bare form `for x in xs { body }` is **map** (produces a collection of body
results). The fold form `for x in xs, acc = init { body }` is **fold**
(produces the final `acc`). The parser distinguishes map vs fold by the
presence of the `, acc = init` clause (spec §12.3, ADR-0074 Negative). `for`
desugars to a `rec` region that calls `Iterator.next` and dispatches via
`match`/`|||` (ID.6). The `Iterator` trait (ADR-0075) is required.

### 4.18 `rec` (spec §12.1, Correction 2)

```text
rec_expr      ::= 'rec' block                         -- contextual {} => block (ID.11)
```

`rec` introduces a **recursive computation region** (Correction 2), not a
recursive arrow. Bindings inside may depend on each other cyclically; the
compiler constructs the feedback graph and checks a well-typed fixpoint
(ID.3). The region evaluates to its last binding (or an explicit `return`),
like a graph block.

### 4.19 `return` (spec §7.3, §7.4, ID.14)

```text
return_expr   ::= 'return' expr
```

`return` terminates a path early. Its scope is the **innermost enclosing `~>`**
arrow (ID.14). A `return` inside a nested arrow exits that inner arrow, not any
outer one. Inside `while`/`do while`/`for` bodies (sugar over `rec`), a
`return` exits the enclosing arrow, not just the loop (spec §12.7).

### 4.20 Block (spec §7)

```text
block         ::= '{' binding (sep binding)* sep? '}'
                | '{' binding (sep binding)* sep? expr sep? '}'   -- trailing expr is the value
                | '{' expr sep? '}'                            -- single-expr block
                | '{' '}'                                      -- empty block
sep           ::= NEWLINE | ';'
```

A block is a brace-delimited sequence of bindings (newline/`;` separated)
optionally ending in an expression. The value of a block is the last binding's
value (a final binding both introduces a wire and returns its value, spec
§7.2) or the trailing expression. A bare expression as the final element is
also the block's result. `return` may terminate a path early (§4.19).

### 4.21 `infer` (spec §13.4, ID.10)

```text
infer_expr    ::= 'infer' identifier                  -- infer x: name the inferred type of x
                | 'infer' '(' expr ')'                 -- infer (parse _): type of an arrow expr
```

`infer x` names the inferred type of `x`; `infer (parse _)` names the inferred
type of an arrow expression with a placeholder input. `_` is allowed in
exactly two contexts (ID.10): (1) inside `infer ( ... )`, and (2) as a
wildcard pattern in `match` and destructuring. `f _` is a syntax error.

### 4.22 Type expressions (spec §13, ID.12)

```text
type_expr     ::= name_annotation
                | type_namespace
                | arrow_type
                | row_type

name_annotation ::= identifier ':' type_expr           -- e.g. parse: Str ~> User
type_namespace ::= 'type' '.' identifier              -- type.Str, type.Int, type.Float, type.Bool
arrow_type     ::= type_expr '~>' type_expr           -- A ~> B at type level (ID.12)
row_type      ::= type_expr '|' identifier             -- row variable, e.g. { name: Str | r }
```

Types are structural and inferred (spec §13.3). Explicit annotations are
`name : Type` (spec §13.1). Built-in types are referenced via the `type.`
namespace (spec §13.2). Arrow types use `~>` at the type level (ID.12). Row
variables use `| r` (ID.7, spec §13.6). There is **no `type` declaration
keyword** in v0.1 (ID.15); sum types are library-provided or inferred.

### 4.23 Literals (spec §2.2)

```text
literal       ::= 'true' | 'false'
                | integer_literal
                | float_literal
                | string_literal
```

See §2.2. Literals are language-level (ID.8); operations on literals are
library arrows.

---

## 5. Mapping to ADR-0053 Grammar Rows

This section maps each construct to ADR-0053's data-driven Pratt model. For
each construct we give: the grammar row kind (prefix/infix), the triggering
token kind, the arity, `child_separators`, the `DelimitedShape` (if
delimited), the `LiteralKind` (for literals), the `node_kind`, and the
`desugar` (if it desugars post-parse per ADR-0053 §7).

The row tables use ADR-0053's terminology. Recall (ADR-0053 §2–§6):

- `ChildSeparator ::= Required(String) | Optional(String) | OneOf(Vec<String>)`.
- `DelimitedShape` fields: `open`, `close`, `separator`, `pair` (`{ separator,
node_kind }`), `rest_token`, `open_is_operator_token`, `flatten`,
  `container_kind`.
- `LiteralKind ::= Number | Bool | Null | String{..} | StripAffix{..} | Raw`.
- `AstShapeDef.desugar: Option<DesugarRule { target_kind, rewrite }>` — a
  post-parse rewrite over the node's children.

### 5.1 Literals and identifiers (prefix, arity 0)

```text
Construct        Row     Token                    Arity  LiteralKind      node_kind
-----------      ----    ----                     -----  ------------     ---------
true/false       prefix  token.literal.true/false  0     Bool             bool
integer          prefix  token.literal.integer     0     Number           int
float            prefix  token.literal.float       0     Number           float
string           prefix  token.literal.string      0     String{2,esc}    string
identifier       prefix  token.identifier          0     Raw              var
_ (wildcard)     prefix  token.wildcard            0     Raw              wildcard
```

`atom_payload` dispatches on `kind_def.literal.unwrap_or(LiteralKind::Raw)`
(ADR-0053 §1). `Bool` maps `true`→true, else false. `String` strips
`delim_chars=2` (the quotes) and applies the escape table. Adding a new
literal form (e.g. raw string) is a new `LiteralKind` variant + a token row.

### 5.2 Arrow construction `~>` (infix, arity 2, right-assoc)

```text
Construct  Row    Token         lbp  rbp_right  child_separators  node_kind  desugar
---------  ----   ----          ---  ---------  ---------------  ---------  -------
~>         infix  token.arrow   20   21         []                arrow     arr
```

`~>` is an infix row with `lbp=20 < rbp_right=21` (right-associative, §3.2).
Arity 2: left operand (parsed in **pattern position**, not at `rbp_right` —
see §5.3), right operand (the body, parsed at `rbp_right=21`). No
`child_separators`. The `desugar` rewrites the `arrow` node to the kernel
`arr` node: `arr (λlhs. ⟦rhs⟧)` (spec §17.2).

> **Pattern-position LHS.** The left operand of `~>` is a `pattern`, not a
> full `expr`. ADR-0053's generic infix loop parses the left operand as the
> already-parsed `left` (the accumulator), so the LHS is whatever was parsed
> _before_ the `~>` token at the caller's `rbp`. To enforce pattern position,
> the parser enters a `pattern`-parsing sub-mode for the operand immediately
> preceding `~>`. This is a minor context flag, analogous to the contextual
> `{}` flag (§1.3); it is not a new grammar-row kind. Equivalently, `~>` may
> be modelled as a **prefix** row over the pattern when the pattern is the
> first operand (the point-free case omits it). The binding powers are
> unchanged.

### 5.3 Composition operators (infix, arity 2, left-assoc)

```text
Construct  Row    Token              lbp  rbp_right  child_separators  node_kind  desugar
---------  ----   ----               ---  ---------  ---------------  ---------  -------
>>>        infix  token.seq           40   39         []                seq       Seq
***        infix  token.product       50   49         []                product   first
&&&        infix  token.fanout        50   49         []                fanout    fan-out
|||        infix  token.choice        30   29         []                choice    Choice
```

All four are infix, arity 2, left-associative (`lbp = rbp_right + 1`). No
`child_separators`. `desugar`: `>>>` → kernel `Seq`; `***` → `first` over
product; `&&&` → fan-out (over `first` + `arr`); `|||` → kernel `Choice`
(spec §17.2). Arrow kind signatures for `***`/`&&&`/`|||` at the type level
are open (spec §5.3, follow-up #3).

### 5.4 Arithmetic / library operators (infix, arity 2, left-assoc)

```text
Construct   Row    Token            lbp  rbp_right  child_separators  node_kind  desugar
----------  ----   ----             ---  ---------  ---------------  ---------  -------
+ - * /     infix  token.op.*       70   69         []                app       add/mul/...
== != < >   infix  token.op.eq ...   70   69         []                app       eq/neq/...
<= >= && || infix  token.op.le ...  70   69         []                app       and/or/...
```

All library operators (ID.8) are infix, arity 2, left-associative at level 6
(§3.2). `node_kind: app`; `desugar` rewrites `x + y` to `add [x, y]` (the
library's named arrow applied to a positional literal). The library resolves
the named arrow (`add`, `mul`, `eq`, ...). Prefix forms (`* 2`, `+ 1`) are
**prefix** rows at `prefix_rbp=70` producing an `arr` node (point-free arrow,
ID.8): `* 2` desugars to `x ~> x * 2`.

### 5.5 Option sugar `??` (infix) and `?.` (postfix)

```text
Construct  Row    Token            lbp  rbp_right  child_separators  node_kind  desugar
---------  ----   ----            ---  ---------  ---------------  ---------  -------
??         infix  token.nullish    60   59         []                nullish   match
?.         infix  token.optchain   60   —          []                optchain  >>> ?.
```

`??` is infix, arity 2, left-assoc (level 5). `desugar` rewrites `a ?? b` to a
`match` node over the option sum: `match a { some: value, none: b, _: b }`
(A.3).

`?.field` is a **postfix** infix row: arity 2 where the second operand is a
single `identifier` (the field name), parsed at `rbp_right` not applicable
(the field is a raw identifier, not an expression). `lbp=60`. `desugar`
rewrites `x?.field` to `x ~> (?.field)` composed via `>>>` (A.4); a chain
`x?.a?.b` desugars to `x ~> (?.a >>> ?b)`.

### 5.6 Field access and indexing (postfix, level 8)

```text
Construct    Row    Token            lbp  rbp_right  DelimitedShape                        node_kind  desugar
-----------  ----   ----             ---  ---------  ------------------------------------  ---------  -------
.field       infix  token.dot        90   —          — (single identifier operand)          field      arr
[expr]       infix  token.lbracket    90   —          open_is_operator_token:true,close:], flatten:true  arr
```

`.field` is a postfix infix row: the operator is `token.dot`, the single
operand is an `identifier` (the field name), `lbp=90`. `node_kind: field`;
`desugar` to `arr (λobj. obj.field)` (spec §17.2).

`[expr]` (indexing) is a postfix infix row with a `DelimitedShape`:
`open_is_operator_token: true` (the `[` is the operator token, already
consumed), `close: token.rbracket`, `separator: token.comma` (unused for a
single index but permitted), `flatten: true` (the index expression is spliced
as the single child). `node_kind: index`; `desugar` to
`arr (λobj. obj[val])` (spec §17.2).

### 5.7 Application / juxtaposition (infix, level 7)

```text
Construct     Row    Token                 lbp  rbp_right  DelimitedShape                    node_kind  desugar
------------  ----   ----                  ---  ---------  --------------------------------  ---------  -------
application   infix  <operand-leading>     80   79         (see below)                       call       —
```

Application is juxtaposition: there is no explicit operator token. ADR-0053
models it as an infix row keyed by the **following operand's leading token**
(an identifier, literal, `(`, `[`, `{` in record position, or a keyword prefix
form). `lbp=80, rbp_right=79` (left-assoc, level 7). The "operator" is the
absence of an operator — the parser, after parsing an atom, checks whether the
next token can begin an operand; if so and `80 >= rbp`, it consumes it as the
argument and produces a `call` node.

For **positional argument** `add [a, b]`, the argument is a `positional_literal`
(prefix row, §5.8), so application is `call(add, [positional_literal [a,b]])`.
For a parenthesized argument form (if used), the argument is a `paren` prefix
row with `DelimitedShape { open_is_operator_token: true, close: token.rparen,
separator: token.comma, flatten: true, container_kind: args }` — the
`flatten: true` case of ADR-0053 §4, producing `call { children: [callee,
arg1, arg2, ...] }` with no eval changes. **No auto-currying** (ID.2):
`add a b` is a syntax error; multi-arg application requires the explicit
positional structure.

### 5.8 Record and positional literals (prefix + delimited)

```text
Construct            Row     Token           Arity  DelimitedShape                                              node_kind
-----------------   ----    ----            -----  ---------------------------------------------------------   ---------
record_literal       prefix  token.lbrace     1     open:{ (op token), close:}, sep:comma/newline,               record
                                          pair:{sep:colon, node_kind:entry}, rest_token:ellipsis,
                                          open_is_operator_token:true, flatten:false
positional_literal   prefix  token.lbracket   1     open:[ (op token), close:], sep:comma/newline,               positional
                                          rest_token:ellipsis, open_is_operator_token:true, flatten:false
paren (if used)      prefix  token.lparen     1     open:( (op token), close:), sep:comma,                       paren/tuple
                                          open_is_operator_token:true, flatten:true
```

These are the `array`/`object`/`paren` cases of ADR-0053 §3. `open_is_operator_token:
true` means the open delimiter is the prefix/infix token itself (already
consumed by `cursor.advance()`), so `parse_delimited_block` skips the
open-consume step. `rest_token: Some("token.ellipsis")` (ADR-0053 §5) handles
spread: when the next token matches `rest_token`, `parse_delimited_block`
parses a bare expression and pushes it as a regular element (`...a` → spread
element). `pair: { separator: token.colon, node_kind: entry }` (ADR-0053 §3)
handles record fields `name : expr` and computed keys `[key] : expr`; the
shorthand `name` (no `:`) is an `entry` with the key equal to the value
identifier. `flatten: false` for record/positional (they emit their own
container node); `flatten: true` for `paren`/call-args (splice into parent).

`desugar`: record/positional literals are construction forms. Spread
(`...expr`) is a construction form, **not** control-flow sugar (spec §11.5) —
it does not desugar to `match`/`rec`; the kernel sees it as an `arr` node that
merges structural values (spec §17.2).

### 5.9 `if` — two-branch (prefix, arity 3) and multi-way (prefix + delimited)

**Two-branch `if`** (spec §8.1):

```text
Construct   Row     Token               Arity  child_separators                              node_kind  desugar
----------  ----    ----                -----  -------------------------------------------   ---------  -------
if          prefix  token.keyword.if    3      [Optional("then")?, Required("else")]        if        match
```

Per ADR-0053 §2, `if` is a prefix row with arity 3 (cond, then, else) and
`child_separators`. The spec's two-branch form is `if cond then else else_expr`
where `then` is **optional** (the spec uses juxtaposition: `if cond expr else
expr`, with no `then` keyword — the then-branch is simply the expression after
the condition). So `child_separators` is effectively
`[Optional("token.keyword.then"), Required("token.keyword.else")]`, but since
v0.1 has no `then` keyword, the first separator is `Optional` and never
consumed; the then-branch is parsed as the second child directly. The
`desugar` (ADR-0053 §7) rewrites the `if` node to a `match` node with two `arm`
children (`true: then`, `_: else`), matching the kernel `|||`/`choice`
routing (spec §17.2). The parser emits the honest `if` node; the desugar pass
rewrites it.

The then-branch and else-branch may each be a **block** (when `{` follows in
block-expecting context, ID.11) or an expression. The else-branch may be
another `if` (else-if chain).

**Multi-way `if`** (Addendum A.7):

```text
Construct      Row     Token               Arity  DelimitedShape                                node_kind  desugar
-----------    ----    ----                -----  -------------------------------------------   ---------  -------
multi-way if   prefix  token.keyword.if    1      open:{ (op token? — see note), close:},         if        nested if
                                                  sep:comma/newline, pair:{sep:colon, node_kind:guard_arm}
```

The multi-way form is `if { c1: e1, c2: e2, _: e3 }`. The parser detects it by
the token immediately after `if` being `{` (A.7). It is a prefix row with a
**trailing delimited block** of guard arms: `DelimitedShape` with
`close: token.rbrace`, `separator: token.comma` (or newline), `pair: {
separator: token.colon, node_kind: guard_arm }`. Each `guard_arm` is
`expr : expr` (or `_ : expr`). `desugar` rewrites the multi-way `if` to nested
two-branch `if`/`else` (A.7), which then each desugar to `match`.

> **Note on `open_is_operator_token`.** In the multi-way form the `{` is _not_
> the `if` operator token itself (it follows `if`), so
> `open_is_operator_token: false` and `parse_delimited_block` consumes the
> `{`. This differs from the record-literal case (§5.8) where `{` _is_ the
> prefix token. The two `if` forms share the `token.keyword.if` prefix token
> but differ in whether the next token is `{` (multi-way, delimited block
> child) or an expression (two-branch, separated operands). This is a
> **prefix-row dispatch on the _following_ token**, which ADR-0053's
> `lookup(token, Prefix)` does not natively express — see §5.14 for the
> special-case analysis.

### 5.10 `match` (prefix + delimited arms)

```text
Construct  Row     Token                Arity  DelimitedShape                              node_kind
---------  ----    ----                 -----  -----------------------------------------   ---------
match      prefix  token.keyword.match  2      (last child) open:{, close:},               match
                                                sep:comma/newline, pair:{sep:colon, node_kind:arm}
```

`match` is a prefix row with arity 2: the scrutinee `expr` (child 0) and the
trailing delimited block of arms (child 1, the `delimited` last child per
ADR-0053 §"What is already generic"). `DelimitedShape`: `open: token.lbrace`
(`open_is_operator_token: false` — the `{` follows the scrutinee, it is not
the `match` token), `close: token.rbrace`, `separator: token.comma` (or
newline), `pair: { separator: token.colon, node_kind: arm }`. Each arm is
`pattern : expr` (or `_ : expr`). The outer `{}` is the match body
(block-like, ID.11); any `{}` inside a pattern position is a record pattern.

`desugar`: `match v { p: e }` desugars to `arr v >>> choice ...` (pattern
dispatch via `|||`, spec §17.2). Exhaustiveness is checked post-parse (ID.13).

### 5.11 `while`, `do while`, `for`, `rec` (prefix + delimited block)

```text
Construct    Row     Token                  Arity  child_separators / DelimitedShape            node_kind  desugar
----------   ----    ----                   -----  -----------------------------------------   ---------  -------
while        prefix  token.keyword.while    2      child 0: cond expr; child 1: block (delimited)  while    rec
do while     prefix  token.keyword.do       2      child 0: block (delimited); child_separators[0]=Required("while"); child 1: cond  do_while  rec
for (map)    prefix  token.keyword.for      3      child_separators:[Required("in")]; child 2: block (delimited)  for_map  rec
for (fold)   prefix  token.keyword.for      5      child_separators:[Required("in"), Required(","), Required("=")]; child 4: block  for_fold  rec
rec          prefix  token.keyword.rec      1      child 0: block (delimited)                    rec       Loop
```

`while cond { body }`: prefix, arity 2. Child 0 is the condition `expr`; child
1 is the trailing delimited block (`DelimitedShape { open: token.lbrace,
close: token.rbrace, ... }`, the block grammar of §4.20). The no-block form
`while cond body` has child 1 as a bare `expr` (no `delimited`).
`child_separators: []` (the condition and body are juxtaposed). `desugar` to a
`rec` region with implicit feedback (A.1).

`do { body } while cond`: prefix, arity 2. Child 0 is the block (delimited);
`child_separators[0] = Required("token.keyword.while")`; child 1 is the
condition `expr`. `desugar` to a body-first `rec` region (A.6).

`for x in xs { body }` (map): prefix, arity 3. Child 0 is the loop variable
`identifier`; `child_separators[0] = Required("token.keyword.in")`; child 1
is the iterable `expr`; child 2 is the trailing delimited block.
`desugar` to a `rec` region + `Iterator.next` + `match`/`|||` (A.2, ID.6).

`for x in xs, acc = init { body }` (fold): prefix, arity 5. Child 0 is the
loop variable; `child_separators[0] = Required("token.keyword.in")`; child 1
is the iterable; `child_separators[1] = Required("token.comma")`; child 2 is
the accumulator `identifier`; `child_separators[2] = Required("token.assign")`;
child 3 is the init `expr`; child 4 is the trailing delimited block.
`desugar` to a `rec` fold (A.2). The map-vs-fold distinction is the presence
of the `, acc = init` clause (§6.3).

`rec { block }`: prefix, arity 1. Child 0 is the trailing delimited block.
`desugar` to the kernel `Loop` (Paterson `loop`, ID.3, spec §17.2).

### 5.12 `return` (prefix, arity 1)

```text
Construct  Row     Token                 Arity  child_separators  node_kind  desugar
---------  ----    ----                  -----  ---------------   ---------  -------
return     prefix  token.keyword.return  1      []                return     early-exit
```

`return expr` is a prefix row, arity 1 (the expression). `node_kind: return`.
`desugar`: an early-exit path through the graph (spec §16, §7.3). Scope is the
innermost enclosing `~>` (ID.14).

### 5.13 `infer` (prefix, arity 1)

```text
Construct  Row     Token                 Arity  child_separators  node_kind  desugar
---------  ----    ----                  -----  ---------------   ---------  -------
infer      prefix  token.keyword.infer   1      []                infer      —
```

`infer x` and `infer ( expr )` are prefix rows, arity 1. The operand is an
`identifier` or a parenthesized expression (which may contain `_`, ID.10).
`node_kind: infer`. No desugar (it is a type-level form). The precise typing
rule for `infer (parse _)` is unspecified in v0.1 (spec §17.3, ADR-0074
Risks).

### 5.14 Constructs outside ADR-0053's Pratt expressiveness

ADR-0053 §"Scope boundary" states the honest claim: _for any construct whose
parse structure is a Pratt prefix/infix with separated operands and at most
one trailing delimited block, no parser code change is needed._ The following
v0.1 constructs sit at or beyond that boundary and require analysis:

**a) Multi-way `if` (prefix dispatch on the following token).** The two `if`
forms (two-branch vs multi-way) share the `token.keyword.if` prefix token but
differ in whether the next token is `{` (multi-way, trailing delimited
guard-arm block) or an expression (two-branch, separated operands). ADR-0053's
`lookup(token, Prefix)` keys only on the prefix token, not on the _following_
token. This is a **dispatch on the token after the prefix token**, which is
not natively expressed by a single grammar row.

- _Resolution._ This fits ADR-0053 with a **minor schema extension or a
  one-token lookahead in the prefix path**: the prefix row for
  `token.keyword.if` carries _both_ shapes (separated-operand and
  trailing-delimited), and the parser chooses based on whether the next
  token is `{`. This is analogous to the contextual `{}` flag (§1.3) — a
  one-bit context decision, not a new grammar-row kind. Alternatively, two
  prefix rows keyed by `(token.keyword.if, Prefix)` with a guard on the
  next token. This is within the spirit of ADR-0053 (the delimited-block
  machinery already exists, ADR-0053 §"What is already generic") but
  requires the prefix path to peek one token. It is **not** a full
  special-case branch like the five ADR-0053 removes; it is a data-driven
  dispatch on a lookahead token. An implementer should add a
  `prefix_lookahead: Option<String>` field to `GrammarRow` (or a
  `DelimitedShape` on the prefix row that is only consulted when the next
  token matches `open`), keeping the change data-driven.

**b) `for ... in ... , acc = init` (two clauses before the trailing block).**
The fold form has _five_ children with three `child_separators` _before_ the
trailing delimited block: `for x in xs , acc = init { body }`. ADR-0053's
prefix loop (§"Resulting `expression_inner`") parses `normal = arity -
(delimited ? 1 : 0)` separated operands, consuming `child_separators[i]`
between them, then the trailing delimited block. The fold form has
`normal = 4` (x, xs, acc, init) with `child_separators = [Required("in"),
Required(","), Required("=")]` (3 separators between 4 operands), then the
delimited block. **This fits the model exactly**: the prefix loop handles
`normal` separated operands then one trailing delimited block. The map form
has `normal = 2` (x, xs) with `child_separators = [Required("in")]`, then the
block. The map-vs-fold distinction is whether the row has arity 3 (map) or
arity 5 (fold) — i.e. **two different prefix rows**, distinguished by a
lookahead on the tokens after `in` (is there a `,`?). This is the same
one-token-lookahead dispatch as (a). No schema extension beyond the
`prefix_lookahead`/guarded-row mechanism is needed.

**c) `do { body } while cond` (delimited block _followed by_ a separator and
an operand).** Here the delimited block is child 0, _then_ a `Required("while")`
separator, _then_ the condition operand. ADR-0053's prefix loop parses
separated operands _first_, then the trailing delimited block. `do` reverses
this: the delimited block comes first. This is **outside** the
"at-most-one-trailing-delimited-block" shape: the delimited block is not
trailing.

- _Resolution._ `do while` requires either (i) a schema extension allowing
  a `delimited` child in a non-trailing position (a `delimited_child_index`
  field), or (ii) a **special-case prefix handler** for `do` that parses
  the block, consumes `while`, and parses the condition — a single
  construct-specific branch. Given `do while` is the only such construct
  in v0.1, a special-case handler is the honest, contained choice; it does
  not undermine ADR-0053's generic property for the rest of the grammar.
  Alternatively, model `do` as a prefix row of arity 1 (the block) whose
  `desugar`/post-parse expects a trailing `while cond` — but this pushes
  the condition into a sibling parse, which is awkward. The cleanest
  data-driven option is a `delimited_child_index: Option<usize>` field on
  `AstShapeRef` (defaulting to "last"), generalizing the trailing-block
  assumption to "the delimited child is at this index." That is a small,
  honest schema extension; it is **not** required for any other v0.1
  construct.

**d) `match` arms and multi-way `if` guard arms with `:` pair separator.**
These use `pair: { separator: token.colon, node_kind: arm }` in the
`DelimitedShape`, which ADR-0053 §3 already supports (the `object` case uses
`pair: { separator: token.colon, node_kind: entry }`). So `match` and
multi-way `if` arms **fit** the model without extension. (Listed here only to
confirm they are _not_ problematic.)

**e) List comprehensions, multi-block constructs, guard patterns.** Per
ADR-0053 §"Scope boundary", these are **out of scope** for v0.1 (§8). They are
not in the grammar.

**Summary.** The v0.1 surface is almost entirely within ADR-0053's
Pratt-expressible range. The two honest exceptions are: (a) prefix-row
dispatch on the _following_ token (multi-way `if`, `for` map-vs-fold), which
needs a one-token lookahead / guarded-row mechanism; and (c) `do while`,
whose delimited block is non-trailing, which needs either a
`delimited_child_index` schema field or a single construct-specific handler.
Neither undermines the generic property for the rest of the grammar.

---

## 6. Disambiguation Rules

### 6.1 Contextual `{}` — full decision procedure (ID.11)

A `{` token begins a **block** iff the parser is in a block-expecting context
(§1.3): immediately after `~>`, `if cond`, `else`, `match val`, `while cond`,
`for ...`, `rec`, or `do`. In all other positions (value/pattern position) a
`{` begins a **record**. In `match val { ... }` the outer `{}` is the match
body (block-like, holding arms); any `{}` inside a pattern position is a
record pattern.

The parser maintains a one-bit `block_expected` flag:

- **Set** when consuming `~>`, the condition of a two-branch `if`, `else`,
  the scrutinee of `match`, the condition of `while`, the header of `for`,
  `rec`, or `do`.
- **Cleared** when entering a value operand (an expression position that is
  not one of the above) or a pattern operand.
- When the next token is `{` and `block_expected` is set, parse a `block`;
  otherwise parse a `record_literal`.

This is the single context-sensitive rule (§1.3).

### 6.2 `if` two-branch vs multi-way

Inspect the token immediately after `if` (A.7):

- If it is `{`, the form is **multi-way** (`if { guard_arm ... }`). Parse the
  delimited guard-arm block.
- Otherwise, the form is **two-branch**. Parse the condition `expr`, the
  then-branch (block if `{` follows, else an expression), then require `else`
  and parse the else-branch (block if `{` follows, else an expression, or
  another `if` for an else-if chain).

The `:` after the condition is not a disambiguator (it is not an infix
operator at the expression level). The presence of `{` immediately after `if`
is the sole disambiguator.

### 6.3 `for` map vs fold

Inspect the tokens after the iterable `xs`:

- If a `,` follows (then `acc = init`), the form is **fold** (arity 5).
- Otherwise, the form is **map** (arity 3).

The type checker enforces that the fold form's body produces a value of the
accumulator's type (ADR-0074 Negative, spec §12.3).

### 6.4 Optional punctuation

- **Commas** between record fields, positional elements, match arms, and
  multi-way `if` guard arms are optional; a newline is an equivalent
  separator (spec §11.1, §9.1, §8.2).
- **Semicolons** between bindings in a `block`, `program`, or `rec` region
  are optional; a newline is an equivalent separator (spec §3.1, §7.1).
- A run of one or more newlines counts as a single separator.

### 6.5 `~>` LHS is a pattern

The left operand of `~>` is parsed in **pattern position** (§4.4, §5.2), not
as a full `expr`. The parser enters pattern-parsing sub-mode for the operand
immediately preceding `~>`. A pattern is a variable, a destructuring pattern,
or a positional structure (§9.2). Point-free arrows omit the LHS (§4.3).

### 6.6 `_` only in `infer` and patterns (ID.10)

`_` is allowed in exactly two contexts (ID.10):

1. Inside `infer ( ... )` — to extract a type from an arrow expression with a
   placeholder input (`infer (parse _)`).
2. As a **wildcard pattern** in `match` arms and destructuring.

`_` is **not** allowed as a function argument: `f _` is a syntax error.
Point-free arrows use explicit `~>` instead (ID.10).

---

## 7. Ambiguities & Resolution

### 7.1 `{ name }` — record literal vs block

`{ name }` could be a record literal (one shorthand field `name`) or a block
containing a bare identifier `name`. **Resolved by position** (ID.11, §6.1):
in value/pattern position it is a record; in a block-expecting context it is a
block. For example, `x ~> { name }` — the `{` follows `~>`, so it is a block
whose value is the wire `name`. But `f { name }` — the `{` is in value
position (an argument to `f`), so it is a record literal with one field.

### 7.2 `a : b` — renaming pattern vs typed binding vs record field

`a : b` appears in three roles:

- **Record field** `a : b` (in a `record_literal`): key `a`, value `b`.
  Resolved by being inside a `{ ... }` record literal.
- **Renaming pattern** `source : local` (in a `record_pattern` or arrow LHS,
  Correction 1): bind source `a` to local `b`. Resolved by being in pattern
  position (the LHS of `~>`, a `match` arm pattern, or a destructuring binding
  LHS).
- **Typed binding** `name : Type` (in a `binding` or annotation): annotate
  `name` with type `Type`. Resolved by being in a binding/annotation position
  (followed by `= expr`).

The positions are disjoint: a `:` in a record literal is a field; a `:` in a
pattern is a renaming; a `:` in a binding header (followed by `=`) is a type
annotation. The parser tracks which position it is in (value, pattern, or
binding-header), so there is no ambiguity.

### 7.3 `if cond expr else expr` — is `expr` the then-branch or part of the condition?

The condition is a full `expr` parsed at the `if` row's `prefix_rbp`. The
then-branch begins after the condition. Since `else` is a keyword (not an
operator), the condition's parse stops at `else` (the `else` token is not a
valid infix continuation). The then-branch is the expression (or block)
between the condition and `else`. There is no ambiguity because `else` is
reserved and terminates the condition parse.

### 7.4 `a, b = b, c` — simultaneous assignment vs two bindings

`a, b = b, c` is a **destructuring binding** whose LHS is a positional
pattern `[a, b]` (written without brackets in the simultaneous-assignment
shorthand) and whose RHS is a positional literal `[b, c]` (spec §10.1). The
`=` distinguishes it from two separate bindings (which would each have their
own `=`). The parser parses the LHS as a comma-separated pattern list up to
`=`, then the RHS as a comma-separated expression list.

### 7.5 `f x >>> g` — application vs composition

Application (juxtaposition) binds tighter than `>>>` (ID.1, §3.2), so
`f x >>> g` parses as `(f x) >>> g` unambiguously via binding powers
(`lbp=80` for application vs `lbp=40` for `>>>`).

---

## 8. What is NOT in the Grammar (Out of Scope for v0.1)

The following are explicitly out of scope for the v0.1 surface (per ADR-0053
§"Scope boundary" and spec §17.3):

- **List comprehensions** `[x | x <- xs, g x]` — two separators in one
  delimited block plus a generator form; not expressible with one
  `DelimitedShape` (ADR-0053). Not in the spec.
- **Multi-block constructs** `match a {} with b {}` — two delimited children;
  ADR-0053's `delimited` field permits only one, as the last child. Not in the
  spec.
- **Guard patterns** `y if g => b` — an optional prefix in a pair's rhs; not
  expressible with the current `PairShape` (ADR-0053). Not in the spec.
- **Arrow kind signatures for `***` / `&&&` / `|||` at the type level** —
  open, follow-up #3 (spec §5.3, §17.3).
- **The precise desugaring specification for the Addendum forms**
  (`while`/`do while`/`for` feedback-wire naming, multi-way `if` nested
  expansion, spread structural override) — follow-up #4 (spec §17.3).
- **The precise typing rule for `infer`** (especially `infer (parse _)`) —
  ADR-0074 Risks, spec §17.3.
- **Row variable support details in the solver** — follow-up #5, ADR-0054
  (spec §17.3). The `| r` row-variable syntax in types (§4.22) is in the
  grammar; the solver details are not.
- **A `type` declaration keyword** — there is none in v0.1 (ID.15). Sum types
  are library-provided or inferred.
- **`trait` / `impl` / `law` declaration syntax** — the keywords are reserved
  (§2.5) but the _declaration grammar_ for explicit trait declarations is
  delegated to ADR-0075 (spec §15). Trait inference is the primary mode
  (annotation-free); explicit declarations are optional sugar whose surface
  form is the authority of ADR-0075, not this grammar. Only the keyword
  reservation is normative here.
- **Block comments** — only `--` line comments are specified (spec §2.3).
- **Auto-currying** — explicitly rejected (ID.2); `add a b` is a syntax error.
- **`_` as a function argument** — explicitly rejected (ID.10); `f _` is a
  syntax error.

Where this grammar is silent and the referenced ADRs are silent, the behavior
is unspecified for v0.1 and must be resolved by the follow-up tasks above
before implementation (spec §17.3).

---

## Related

- [ADR-0053 — Generic Pratt Parser](../../project/adrs/0053-generic-pratt-parser.md)
  — the data-driven Pratt parser model this grammar is expressed against
  (prefix/infix rows, binding powers, `DelimitedShape`, `child_separators`,
  `LiteralKind`, `AstShapeDef.desugar`).
- [ADR-0074 — Arrow Surface Syntax v0.1 — Redesign](../../project/adrs/0074-arrow-syntax-v0_1-surface-redesign.md)
  — the decision of record for the v0.1 surface; source of ID.1–ID.17,
  Correction 1 (destructuring renaming), Correction 2 (`rec` as recursive
  region), and Addendum A.1–A.7 (while, for, do while, `??`, `?.`, spread,
  multi-way `if`).
- [Arrow Language Specification v0.1](./ARROW_LANGUAGE_SPEC_V0_1.md) — the
  authoritative source for the v0.1 surface syntax; every construct in its
  §§1–17 has a grammar rule in this document.
