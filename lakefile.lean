import Lake
open Lake DSL

package «TotemArtifact» where
  leanOptions := #[⟨`autoImplicit, false⟩]

lean_lib «ProofAutomation» where
  roots := #[`ProofAutomation]

@[default_target]
lean_lib «PPTheorems» where
  roots := #[`PPTheorems]
