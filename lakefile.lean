import Lake
open Lake DSL

package «TotemArtifact» where
  leanOptions := #[⟨`autoImplicit, false⟩]
  testDriver := "Tests"

require plausible from git
  "https://github.com/leanprover-community/plausible" @ "v4.28.0"

@[default_target]
lean_lib «ProofAutomation» where
  srcDir := "lean"
  roots := #[`ProofAutomation]

-- End-to-end scenario files: full subtyping-query dumps from Cobb plus
-- targeted tactic-stack experiments. Each root is an independent file
-- (not a library); listing them here gates them on `lake build` so
-- tactic regressions surface in CI instead of rotting silently.
@[default_target]
lean_lib «Scenarios» where
  srcDir := "lean"
  -- Auto-discover: every `lean/Scenarios/*.lean` is picked up. Drop a file
  -- in and CI builds it; no lakefile edit needed.
  globs := #[.submodules `Scenarios]

-- Regression test suite for ProofAutomation. `lake test` builds this lib;
-- every test is encoded as elaboration assertions (`example`, `#guard`,
-- `#guard_msgs`), so a build failure means a regression.
@[default_target]
lean_lib «Tests» where
  srcDir := "lean"
  roots := #[`Tests]
