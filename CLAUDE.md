# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Totem is a program synthesis and formal verification system that repairs incomplete OCaml test input generators. It combines three components:

1. **Cobb_Totem** (Rust + Lean 4 submodule) — Parses OCaml programs and generates formal axioms, validated through Lean 4's type checker
2. **Cobb** (OCaml submodule) — Type-checks generators against axioms using coverage types (underapproximation refinement types), then synthesizes repairs via type-guided enumeration
3. **totem_runner** (Rust, root-level) — CLI orchestrator that coordinates both tools

**Pipeline:**
```
OCaml program.ml → [Cobb_Totem] → program.axioms.ml (let[@axiom] decls) → [Cobb] → type-check / synthesis repairs
```

## Build & Run Commands

### totem_runner (from repo root)
```bash
cargo build --manifest-path totem_runner/Cargo.toml
cargo run --manifest-path totem_runner/Cargo.toml -- generate integration_tests/sizedlist/program.ml
cargo run --manifest-path totem_runner/Cargo.toml -- typecheck integration_tests/sizedlist/program.ml
cargo run --manifest-path totem_runner/Cargo.toml -- abduction integration_tests/sizedlist/sizedlist_gen_synth_prog1.ml
cargo run --manifest-path totem_runner/Cargo.toml -- synthesis integration_tests/sizedlist/sizedlist_gen_synth_prog1.ml
```

### Integration tests (from repo root)
```bash
cargo test --test integration_tests                          # all tests
cargo test --test integration_tests test_sizedlist           # single test
cargo test --test integration_tests -- --list                # list tests
```

### Cobb_Totem (from Cobb_Totem/)
```bash
cargo build
cargo test
cargo test test_list_len                                     # single test
cargo run --release -- --export-axioms output.axioms.ml input.ml
```

### Cobb (from Cobb/)

General dune/opam workflow lives in the `ocaml-dune-project` skill. Project-specific entry points:

```bash
dune exec -- bin/main.exe type-check meta-config.json program.ml
dune exec -- bin/main.exe synthesis program.ml
dune exec -- bin/main.exe abduction program.ml
```

### Lean (from Cobb_Totem/ or repo root)
```bash
lake update && lake build aesop && lake build hammer         # setup
lake env lean --stdin                                        # validate Lean code
```

## Architecture

### Cobb_Totem Key Modules (Cobb_Totem/src/)
- `ocamlparser.rs` — Tree-sitter-based OCaml parser
- `prog_ir.rs` — Program IR: TypeDecl, LetBinding, Expression, Pattern, Type
- `spec_ir.rs` — Specification IR: Axiom, Proposition, Parameter, Quantifier
- `axiom_generator.rs` — Core axiom generation from program IR
- `axiom_builder_state.rs` — Builder state machine for axiom construction
- `create_wrapper.rs` — Creates wrapper functions (`{func}_wrapper`) for axioms
- `lean_backend.rs` — Converts IR to Lean 4 syntax via `ToLean` trait
- `lean_validation.rs` — Validates generated Lean code via `lake env lean --stdin`

### Cobb Synthesis Pipeline (Cobb/bin/)
1. `main.ml` — Entry point; commands: `synthesis`, `abduction`, `type-check`, `localize`
2. `preprocess.ml` — Prepares source code and extracts function structure
3. `localization.ml` — Identifies repair locations using type information
4. `pieces.ml` — Extracts seeds and components for synthesis
5. `blocks.ml` — Core enumeration logic coordinating synthesis
6. `postprocess.ml` — Reconstructs final program from synthesized repairs
7. `enumeration/` — Type-guided bottom-up enumerative synthesis engine

### Cobb Type System (Cobb/underapproximation_type/)
- `backend/` — Z3 SMT solver interface
- `typing/` — Type checking (`termcheck.ml`) and synthesis (`termsyn.ml`)
- `subtyping/` — Refinement type subtyping via SMT

### Integration Tests (integration_tests/)
Each test directory contains: `program.ml` (spec), `meta-config.json` (config), `*_gen.ml` (complete generator), `*_gen_synth_prog*.ml` (incomplete variants for synthesis), and supporting type/axiom files. Tests use `ilist = Nil | Cons of int * ilist` as the primary data type.

## Axiom Format

Generated axioms are OCaml `let[@axiom]` declarations:
```ocaml
let[@axiom] len_0 (l : ilist) (res : int) =
  ((len_wrapper l res))#==>((l)#==(Nil))#==>((0)#==(res))
```
- Universal params: `(name : type)`, existential: `((name [@exists]) : type)`
- Operators: `#==>` (implication), `#==` (equality)
- Wrapper functions normalize function results for axiom comparison

## Configuration

- `meta-config.json` in each test directory controls type checking: paths to `coverage_typing`, `normal_typing`, `data_type_decls`, `templates`, and `program_axioms` files
- `Cobb/underapproximation_type/data/predefined/lean_preamble.lean` — prepended to all dumped Lean subtyping query files; contains type declarations, helper predicates, method predicate definitions, and imports (including `ProofAutomation` for custom tactics)
- When encountering `(func: none) =? none` errors, add the function's type signature to `normal_typing.ml` and `coverage_typing.ml`

## Prerequisites

- **Rust** (2024 edition) with Cargo
- **OCaml 5.1.0+** — toolchain setup via the `ocaml-dune-project` skill
- **Z3** (4.15.1) SMT solver
- **Lean 4** (v4.28.0) with Lake
- Submodules: `git submodule update --init --recursive`

## Guidelines

- Do not modify `.gitignore`
- Cobb and Cobb_Totem are separate git submodules; changes to either should be coordinated through the user
- **External tool wraps (Z3, `lake`, `dune`, etc.) propagate failures as explicit error variants — never collapse to `Unknown`/`None`/"no result".** Look at *both* stdout and stderr, and distinguish errors *before* the verdict (fatal — query/file is malformed) from errors *after* the verdict (informational — e.g. `(get-model)` failing on an `unknown`).
- **A model/output round-trip must validate.** When feeding a tool's output back into the same tool (e.g. Z3's `(get-model)` response into a follow-up query), confirm the result is well-formed for re-consumption. Z3 in particular emits `:named` annotations as standalone `(define-fun NAME () Bool ...)` entries that reference functions defined later in the same model, breaking SMT-LIB's "define before use" rule — filter to only keep model entries for symbols actually declared in the original preamble.
- **Validate constructed SMT queries before sending.** `smt_tools/src/validate.rs` runs forward-reference, `set-option`-after-`set-logic`, and duplicate-`:named` checks on every query inside `run_z3`, on top of full SMT-LIB parsing via `smtlib-lowlevel` (which catches paren imbalance, malformed forms, etc. "for free"). Keep validation active — when you build a query by hand (manual `format!(...)` constructions, ad-hoc concatenation), `run_z3` will surface malformedness as a `Z3Result::Error` at the call site rather than via a silent `Z3Result::Unknown` downstream. If validation returns an error, fix the query builder; the offending query is dumped to `/tmp/smt_tools_invalid_<pid>.smt2` for inspection. `smtlib-lowlevel` 0.3.0 has a `todo!()` in its `bool` parse impl — the local fork at `smt_tools/vendor/smtlib-rs/` (wired via `[patch.crates-io]`) fixes this; rely on the patched fork rather than working around bool-option panics in calling code.
- **Two-phase queries for models.** Never speculate `(get-model)` after a non-Sat verdict. Run check-sat first; only if the result is Sat should you re-issue the query with `(get-model)` appended. The strict error policy will otherwise classify `(get-model)` on an `unknown` as a hard error. There is no library helper for this pattern — implement at the call site.
- **Always verify Lean code changes build** — after modifying any `.lean` file, confirm it compiles before claiming the change is correct (see `lean/CLAUDE.md` for commands).
- **Markdown TODO files are working lists, not changelogs.** Use `- [ ]` checkbox bullets (not numbered lists). When an item is finished, **delete the entry entirely** — do not flip it to `[x]`, do not leave a "Done: …" trailer. History lives in git; stale `[x]` rows are noise. The same applies to items explicitly declined as wontfix: delete rather than tombstone, capturing reasoning (if worth preserving) in a commit message or code comment. Cross-references between items should use the short title, never a position-based handle like "#3" or "item 2" that breaks under reordering.
- **No TODOs or forward-looking commentary in code.** Inline `TODO:` / `FIXME:` comments, "v1.5 will…" predictions, "tracked in TODO_*.md" pointers, "see PLAN_*.md for open work" hints, and user-facing scaffold/error text that references future work all go in the appropriate markdown file (`TODO.md`, `lean/TODO_*.md`, `PLAN_*.md`) instead. Code comments should explain *current* behavior, invariants, or non-obvious *why* — not roadmap. If you find yourself writing a TODO at a call site, add a `- [ ]` bullet to the matching markdown file and leave the code unannotated. Pointers in the *other* direction are fine: a markdown TODO entry can name the file/symbol it refers to.
- **No defensive over-commentary.** A comment earns its place only if a reader of the code alone would be *surprised* by the behavior. Do not enumerate every branch/edge case the function handles, list what is *not* a concern, restate what the code already says in prose, or pre-empt review questions ("this is intentional because…", "this path is safe because β fires first…"). Findings surfaced during code review belong in the PR description or commit message, **not** transplanted above the function as defensive documentation. Target ratio: a 15-line function does not get a 15-line docblock. A real heuristic blind spot gets one line, only if it would actually trip up a reader of the code.

### Documentation
- One README per feature, placed near the code it describes
- Focus on "what to do" (usage, commands, troubleshooting), not "what was done"
- Don't create separate MIGRATION.md, SUMMARY.md, INDEX.md, or IMPLEMENTATION_STATUS.md files
- Do not create root-level docs that duplicate submodule-specific documentation
