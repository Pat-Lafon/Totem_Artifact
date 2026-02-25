# Integration Tests

Automated testing for Totem axiom generation, type checking, and synthesis using list-based generator benchmarks with the `ilist` data type.

## Test Benchmarks

- **duplicate_list** - Generator producing lists with single element value
- **even_list** - Generator producing lists with only even integers
- **sizedlist** - Generator producing lists of bounded size
- **sortedlist** - Generator producing sorted lists
- **uniquelist** - Generator producing lists with unique elements

Each benchmark includes multiple program variants (prog1-progN) representing different incomplete implementations for synthesis testing.

## Quick Start

Run all integration tests:

```bash
cargo test --test integration_tests
```

Run a specific test:

```bash
cargo test --test integration_tests test_sizedlist
```

List all available tests:

```bash
cargo test --test integration_tests -- --list
```

## Test Phases

Each test runs two main phases, with optional synthesis variants:

### 1. Generate (Axiom Extraction)

Extracts axioms from the OCaml program using Cobb_Totem and saves to `program.axioms.ml`

### 2. Typecheck (Axiom Validation)

Validates the program against the generated axioms using Cobb's type checker

### 3. Synthesis (with Abduction)

For each incomplete program variant:
- **Abduction**: Infers missing coverage (what inputs the variant fails to produce). Results saved to `variant.ml.abd`
- **Synthesis**: Uses the inferred coverage to repair the incomplete program

## Manual Testing (Using totem_runner CLI)

```bash
# Generate axioms
cargo run --manifest-path totem_runner/Cargo.toml -- generate integration_tests/sizedlist/program.ml

# Typecheck with axioms
cargo run --manifest-path totem_runner/Cargo.toml -- typecheck integration_tests/sizedlist/program.ml

# Run abduction on a synthesis variant to infer missing coverage
cargo run --manifest-path totem_runner/Cargo.toml -- abduction integration_tests/sizedlist/sizedlist_gen_synth_prog1.ml

# Run synthesis (includes abduction step automatically)
cargo run --manifest-path totem_runner/Cargo.toml -- synthesis integration_tests/sizedlist/sizedlist_gen_synth_prog1.ml

# Clean up generated axiom files
cargo run --manifest-path totem_runner/Cargo.toml -- clean integration_tests/sizedlist/program.ml
```

## Test Structure

Each test directory contains:

```
integration_tests/<test_name>/
├── program.ml                         # Main program for axiom generation/type-check
├── <test_name>_gen.ml                # Complete witness generator
├── <test_name>_gen_synth_prog1.ml    # Variant 1 (synthesis task)
├── <test_name>_gen_synth_prog2.ml    # Variant 2
├── <test_name>_gen_synth_prog3.ml    # Variant 3
├── ...
├── components.txt                     # List of components for synthesis
├── meta-config.json                   # Cobb type-check configuration
├── program.axioms.ml                  # Generated axioms (let[@axiom] declarations)
├── data_type_decls.ml                 # ilist type definition
├── templates.ml                       # Synthesis templates
├── normal_typing.ml                   # OCaml signatures
└── coverage_typing.ml                 # Coverage type definitions
```

## Test Phases Explained

### Generate Phase

```
OCaml program (program.ml)
         ↓
    [Cobb_Totem]
         ↓
   program.axioms.ml (let[@axiom] declarations)
```

Extracts formal axioms from the OCaml program definition and assertion.

### Typecheck Phase

```
program.ml + program.axioms.ml + meta-config.json
         ↓
     [Cobb Type Checker]
         ↓
    Type checking results
```

Validates that the program satisfies the type constraints specified in the assertion.

### Synthesis Phase (with Abduction)

```
Incomplete program variant (e.g., prog2.ml)
         ↓
    [Cobb Abduction]
         ↓
   variant.ml.abd (missing coverage)
         ↓
    [Cobb Synthesizer]
         ↓
    Synthesized repairs
```

For each incomplete program variant:
1. **Abduction** infers what inputs the variant fails to produce based on the axioms
2. **Synthesis** uses the inferred coverage to repair the incomplete program by filling in `Err` and `Exn` terms

## Test Names

Available tests in `cargo test --test integration_tests`:
- `test_duplicate_list`
- `test_even_list`
- `test_sizedlist`
- `test_sortedlist`
- `test_uniquelist`
- `test_list_length` (existing)
- `test_list_sorted` (existing)

## Adding New Tests

1. Create a new directory: `integration_tests/<test_name>/`
2. Add `program.ml` with OCaml function and assertion
3. Copy supporting files from an existing test:
   - `meta-config.json` (update paths to point to your directory)
   - `data_type_decls.ml`, `templates.ml`, `normal_typing.ml`, `coverage_typing.ml`
   - `axioms.ml` (may need customization for your data structure)
4. Run: `make test-<test_name>`

## Troubleshooting

**"dune not found"**
- Install OCaml and dune: `brew install opam` then `opam install dune`

**"Submodule not found"**
- Initialize submodules: `git submodule update --init --recursive`

**"meta-config.json not found"**
- Ensure `meta-config.json` exists in the test directory with correct paths

**Synthesis fails with type errors**
- Check that `axioms.ml` correctly defines all predicates used in the program
- Verify `data_type_decls.ml` matches the types used in `program.ml`

## Data Type: ilist

All list tests use the custom `ilist` type for list synthesis:

```ocaml
type ilist = Nil | Cons of int * ilist
```

This concrete type representation allows Cobb_Totem to generate specific axioms about list structure.

## Files Reference

### Configuration
- `meta-config.json` - Metadata for type checking and synthesis (paths, rlimits)
- `components.txt` - List of component names available for synthesis engine

### Type Definitions
- `data_type_decls.ml` - OCaml data types (ilist)
- `normal_typing.ml` - OCaml function signatures
- `coverage_typing.ml` - Coverage type annotations
- `templates.ml` - Axiom templates for synthesis

### Programs
- `program.ml` - Specification program with axiom assertions
- `program.axioms.ml` - Generated axioms (produced by Cobb_Totem)
- `<test_name>_gen.ml` - Complete witness generator (typecheck target)
- `<test_name>_gen_synth_prog*.ml` - Incomplete variants for synthesis tasks
