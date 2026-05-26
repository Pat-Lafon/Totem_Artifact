import Lake
open Lake DSL

package «TotemArtifact» where
  leanOptions := #[⟨`autoImplicit, false⟩]
  testDriver := "Tests"

require plausible from git
  "https://github.com/leanprover-community/plausible" @ "v4.28.0"

lean_lib «ProofAutomation» where
  srcDir := "lean"
  roots := #[`ProofAutomation]

-- Failing subtyping queries we want to import (for PBT counterexample search).
-- Each is its own root because they are independent dump files, not a library.
lean_lib «test_rbtree_typecheck_timeout» where
  srcDir := "lean"
  roots := #[`test_rbtree_typecheck_timeout]

-- Regression test suite for ProofAutomation. `lake test` builds this lib;
-- every test is encoded as elaboration assertions (`example`, `#guard`,
-- `#guard_msgs`), so a build failure means a regression.
lean_lib «Tests» where
  srcDir := "lean"
  roots := #[`Tests]
