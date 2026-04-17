# SMT Decidability Checker — Design Plan

## 1. Motivation and Problem Statement

The Totem pipeline generates SMT-LIB2 queries (`.smt2` files) encoding coverage type subtyping obligations over algebraic datatypes (`ilist`, `itree`, `irbtree`). Two classes of problems can cause Z3 to return unsound, unexpected, or unpredictable results:

**Problem 1: Ungated Accessors.** SMT-LIB datatype selectors (e.g., `(color t)`, `(head l)`, `(left t)`) are total functions — when applied to a value of the wrong constructor (e.g., `(color rbtleaf)`), they return an arbitrary value of the selector's return sort. This isn't undefined behavior; it produces a "garbage" value that can silently make formulas satisfiable or unsatisfiable in unexpected ways. The correct pattern is to guard every selector application with the appropriate recognizer, e.g., `((_ is rbtnode) t)` must be asserted/implied before `(color t)` is used.

The current Totem output already follows this pattern — accessors like `(= (color t) c)` appear in conjunctions with `((_ is rbtnode) t)`. However, there is no automated enforcement, and changes to the OCaml backend (`litencoding.ml` applies accessors based on type information, not guarding logic) could introduce ungated uses.

**Problem 2: Quantifier Alternation.** The decidable fragment of the theory of algebraic datatypes restricts quantifier nesting. Certain alternation patterns (especially `∀∃∀` over datatype-sorted variables) push Z3 outside its decidable fragment, leading to `unknown` results or timeouts. The tool should characterize the alternation depth and warn when it exceeds known-decidable bounds.

## 2. Architecture and Design

### 2.1 Project Structure

An independent Rust crate named `smt_tools`:

```
smt_tools/
  Cargo.toml
  src/
    main.rs              -- CLI entry point
    lib.rs               -- public API for programmatic use
    parser.rs            -- SMT-LIB2 S-expression parser
    ast.rs               -- AST types for SMT-LIB commands and terms
    datatype_info.rs     -- extract datatype declarations
    accessor_check.rs    -- Pass 1: ungated accessor detection
    quantifier_check.rs  -- Pass 2: quantifier alternation analysis
    diagnostics.rs       -- warning/error reporting with locations
```

### 2.2 CLI Interface

```
smt_tools [OPTIONS] <FILE.smt2>

Options:
  --check-accessors     Enable ungated accessor check (default: on)
  --check-quantifiers   Enable quantifier alternation check (default: on)
  --json                Output diagnostics as JSON
  --strict              Treat warnings as errors (non-zero exit code)
  -q, --quiet           Only output errors, not warnings
```

Exit codes: 0 = no issues, 1 = warnings, 2 = errors, 3 = parse failure.

## 3. SMT-LIB Parsing

### 3.1 Commands to parse

Based on actual Totem `.smt2` output:

- `(set-option :key value)` — skip
- `(declare-datatypes ((name arity)) ((constructors...)))` — extract datatype info
- `(declare-fun name (sorts) sort)` — record for context
- `(assert term)` — main payload to analyze
- `(check-sat)` — skip

### 3.2 Term AST

```rust
enum Term {
    Var(String),
    Int(i64),
    Bool(bool),
    App { func: String, args: Vec<Term> },
    Recognizer { constructor: String, arg: Box<Term> },  // (_ is C) t
    Selector { name: String, arg: Box<Term> },            // (color t)
    Not(Box<Term>),
    And(Vec<Term>),
    Or(Vec<Term>),
    Implies(Box<Term>, Box<Term>),
    Eq(Box<Term>, Box<Term>),
    Ite(Box<Term>, Box<Term>, Box<Term>),
    Let { bindings: Vec<(String, Term)>, body: Box<Term> },
    Forall { vars: Vec<(String, Sort)>, body: Box<Term> },
    Exists { vars: Vec<(String, Sort)>, body: Box<Term> },
}
```

The critical step is distinguishing **selectors** from ordinary function applications, which requires the datatype info extracted from `declare-datatypes`.

### 3.3 Parser approach

Hand-written recursive descent on S-expressions (no external crate needed). Two phases:

1. **Tokenize** → `LParen`, `RParen`, `Symbol`, `Int`, `Keyword` (`:qid` etc.), `String`
2. **S-expression tree** → `Atom(String)` | `Int(i64)` | `List(Vec<Sexpr>)`
3. **Command dispatch** → pattern-match top-level S-exprs
4. **Term construction** → convert S-exprs inside `assert` bodies into `Term` AST, using datatype info to classify selectors vs. uninterpreted functions

### 3.4 Datatype extraction

From:
```smt2
(declare-datatypes ((irbtree 0))
  (((rbtleaf) (rbtnode (color Bool) (left irbtree) (value Int) (right irbtree)))))
```

Extract:
```rust
struct DatatypeInfo {
    name: String,                          // "irbtree"
    constructors: Vec<ConstructorInfo>,
}

struct ConstructorInfo {
    name: String,                          // "rbtnode"
    recognizer: String,                    // "is_rbtnode" (convention: "is_" + name)
    selectors: Vec<(String, String)>,      // [("color","Bool"), ("left","irbtree"), ...]
}
```

Recognizer names follow the `is_<constructor>` convention from `dtencoding.ml:49`. In the `.smt2` output, recognizers appear as `((_ is rbtnode) t)`.

## 4. Pass 1: Accessor Safety (Ungated Selector Detection)

### 4.1 Definition of "guarded"

A selector application `(sel t)` for selector `sel` of constructor `C` is **guarded** if a recognizer `((_ is C) t)` is guaranteed to hold whenever `(sel t)` is evaluated.

Guarding contexts:

1. **Direct conjunction**: `(and ... ((_ is C) t) ... (sel t) ...)` — recognizer is a sibling conjunct.
2. **Implication antecedent**: `(=> ((_ is C) t) body)` where `(sel t)` appears in `body`, or `(=> (and ... ((_ is C) t) ...) body)`.
3. **Nested implication chain**: `(=> P1 (=> P2 ... (sel t)))` where some `Pi` contains `((_ is C) t)`.
4. **Equality guard**: `(= t (C args...))` in guarding position implies `((_ is C) t)`.

### 4.2 Algorithm

Maintain a **guard context** — a set of `(constructor, variable)` pairs known to hold:

```
check(term, guards):
  match term:
    Selector { name, arg: Var(v) } =>
      ctor = lookup_constructor_for_selector(name)
      if (ctor, v) not in guards:
        emit_warning("Ungated accessor: (name v)")

    And(children) =>
      new_guards = extract_recognizers(children)
      for child in children:
        check(child, guards ∪ new_guards)

    Implies(ante, body) =>
      check(ante, guards)
      new_guards = extract_recognizers(ante)
      check(body, guards ∪ new_guards)

    Not(inner) =>
      check(inner, guards)  // guards do NOT propagate through negation

    Let { bindings, body } =>
      // inline let-bindings before analysis
      check(substitute(body, bindings), guards)

    Forall/Exists { vars, body } =>
      check(body, guards)

    _ => recurse with same guards
```

### 4.3 Let-binding inlining

Z3's output uses let-bindings extensively (`a!1`, `a!2`, etc.). Simplest correct approach: **eager inlining** before running the check. The files are small enough (~500 lines) for this to be tractable.

### 4.4 What NOT to flag

- Selectors applied to constructor terms: `(color (rbtnode true rbtleaf 5 rbtleaf))` — trivially safe.
- Uninterpreted functions like `(num_black t h res)` — not selectors.
- Selectors for datatypes not declared in the file.

## 5. Pass 2: Quantifier Alternation Analysis

### 5.1 Background

Decidability depends on quantifier prefix structure over datatype sorts:

| Pattern | Decidable? |
|---------|-----------|
| `∀-only` or `∃-only` | Yes |
| `∃∀` (SAT with universal) | Yes (catamorphism fragment) |
| `∀∃` with base-sort existentials | Generally yes |
| `∀∃∀` over datatype-sorted variables | Potentially undecidable |

### 5.2 Algorithm

Polarity-aware traversal (negation flips quantifier semantics):

```
analyze(term, polarity, path):
  match term:
    Forall { vars, body } =>
      effective = if polarity == Positive then Forall else Exists
      dt_vars = vars.filter(is_datatype_sort)
      analyze(body, Positive, path ++ [(effective, dt_vars)])

    Exists { vars, body } =>
      effective = if polarity == Positive then Exists else Forall
      dt_vars = vars.filter(is_datatype_sort)
      analyze(body, Positive, path ++ [(effective, dt_vars)])

    Not(inner) =>
      analyze(inner, flip(polarity), path)

    Implies(a, b) =>
      analyze(a, flip(polarity), path)  // antecedent has flipped polarity
      analyze(b, polarity, path)

    And/Or(children) =>
      for child in children: analyze(child, polarity, path)

    Let { bindings, body } =>
      analyze(substitute(body, bindings), polarity, path)
```

After collecting all paths, compute:
- Maximum alternation depth (count polarity switches)
- Whether datatype-sorted variables appear at each alternation level
- Pattern string for each path (e.g., "AE", "AEA")

### 5.3 Reporting thresholds

- **Info**: Alternation depth 1 — normal for Totem axioms
- **Warning**: Alternation depth 2+ with only base-sorted alternating variables — usually decidable but may timeout
- **Error**: Alternation depth 2+ with datatype-sorted variables at alternation boundaries — potentially undecidable

### 5.4 Polarity in the Totem pipeline

The final assertion is negated (validity-to-SAT reduction): `(assert (not (forall ...)))`. Under negation, `forall` becomes effectively `exists`, so `(not (forall x. P))` is effectively `(exists x. not P)` — just a SAT query.

## 6. Edge Cases and Limitations

### 6.1 Edge cases to handle

- **Indexed identifiers**: `(_ is rbtnode)` uses SMT-LIB2 indexed syntax
- **Annotated terms**: `(! body :qid name)` — unwrap transparently
- **Quoted symbols**: `|c'|`, `|c''|` — tokenizer handles `|...|` delimiters
- **Nested let-bindings**: recursive inlining required
- **Zero-selector constructors**: `rbtleaf`, `nil` have no selectors — skip

### 6.2 Limitations

- **Semantic guards**: If a guard is established through uninterpreted function chains (e.g., `(P t)` semantically implies `((_ is rbtnode) t)` but not syntactically), the tool produces false positives. This is fundamental to syntactic analysis.
- **Conservative quantifier analysis**: Checks syntactic alternation, not semantic. Some formulas with syntactic alternation are decidable due to formula shape (catamorphism schemes).
- **Post-hoc only**: Analyzes the final `.smt2` file, not the OCaml-level Z3 API calls.

## 7. Integration

### 7.1 Standalone

```bash
cargo run --manifest-path smt_tools/Cargo.toml -- subtyping_temp_file.smt2
```

### 7.2 With totem_runner

Could be invoked as a pre-check step between `smt_format_file` writing the `.smt2` and Z3 solving. Either:
- A `totem_runner check` subcommand
- Called from the integration test suite in `totem_runner/tests/integration_tests.rs`

### 7.3 CI

For each benchmark directory, generate the `.smt2` file and run `smt_tools` on it as part of the integration test suite.

## 8. Example Output

### Well-formed file (no warnings)
```
smt_tools: subtyping_temp_file.smt2
  Accessor check: PASS (0 warnings)
  Quantifier check: PASS
    Max alternation depth: 0 (forall-only)
```

### Ungated accessor
```
smt_tools: bad_query.smt2
  WARNING [accessor:ungated] line 3: Selector 'color' applied to 't' without recognizer guard '(_ is rbtnode)'
    in: (= (color t) true)
    fix: Guard with ((_ is rbtnode) t)
```

### Quantifier alternation
```
smt_tools: deep_query.smt2
  ERROR [quantifier:alternation] lines 2-4: Alternation depth 2 (AEA) with datatype-sorted variables
    Path: forall(t:irbtree) -> exists(u:irbtree) -> forall(v:irbtree)
    This pattern may be outside the decidable fragment.
```

## 9. Key Files

| File | Relevance |
|------|-----------|
| `Cobb/.../backend/dtencoding.ml` | Defines datatype schema (constructors, recognizers, selectors) |
| `Cobb/.../backend/check.ml` | `smt_format_file` (line 46-63) writes the `.smt2` files |
| `Cobb/.../backend/litencoding.ml` | Applies accessors (lines 34-47) — source of potential ungated uses |
| `Cobb/.../subtyping_temp_file.smt2` | Real example output — primary test input |
| `totem_runner/src/main.rs` | Model for CLI structure |
