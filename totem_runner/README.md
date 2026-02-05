# Totem Runner

Integration test runner for axiom verification. Orchestrates Cobb_Totem (axiom generation) and Cobb (type checking).

## Quick Start

From repo root:

```bash
# Generate axioms
cargo run --manifest-path totem_runner/Cargo.toml -- integration_tests/list_length/program.ml generate

# Type-check with axioms
cargo run --manifest-path totem_runner/Cargo.toml -- integration_tests/list_length/program.ml typecheck

# Both in sequence
cargo run --manifest-path totem_runner/Cargo.toml -- integration_tests/list_length/program.ml all

# Clean up generated axioms
cargo run --manifest-path totem_runner/Cargo.toml -- integration_tests/list_length/program.ml clean
```

The program file is required as the first argument (relative to repo root).

## Commands

### generate
Exports axioms from OCaml program using Cobb_Totem `--export-axioms`.

Output: `program.axioms.ml` (let[@axiom] declarations)

### typecheck
Type-checks program with axioms using Cobb's underapproximation_type library.

Loads axioms from `meta-config.json` → `prim_path.axioms` and validates program against axiom constraints.

### all
Runs both commands in sequence: generate → typecheck

### clean
Removes generated axioms file.

## Test Structure

Tests live in `integration_tests/<test_name>/`:

```
integration_tests/list_length/
├── program.ml              # OCaml source
├── meta-config.json        # Cobb config (prim_path.axioms path)
├── program.axioms.ml       # Generated axioms
└── README.md               # Test notes
```

To add a new test:
1. Create `integration_tests/<name>/` directory
2. Add `program.ml` with OCaml type definitions and functions
3. Add `meta-config.json` pointing to axioms file
4. Run: `cargo run --manifest-path totem_runner/Cargo.toml -- integration_tests/<name>/program.ml all`
