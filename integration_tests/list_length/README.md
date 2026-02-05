# List Length Test

Test case: Verify a list length function against type constraints using generated axioms.

## Running

```bash
# From repo root
cargo run --manifest-path totem_runner/Cargo.toml -- integration_tests/list_length/program.ml all
```

See `totem_runner/README.md` for runner documentation.

## Files

- `program.ml` - OCaml list length function
- `meta-config.json` - Cobb type-check configuration
- `program.axioms.ml` - Generated axioms (output of `generate` command)
