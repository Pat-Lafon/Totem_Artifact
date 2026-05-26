import ProofAutomation.Helpers
import ProofAutomation.OcamlFormat
import ProofAutomation.PBT
import ProofAutomation.SearchAxioms
import ProofAutomation.SimpHyps
import ProofAutomation.ProveAxiom
import ProofAutomation.ProposeAxiom
import ProofAutomation.ProposeCounterexample
import ProofAutomation.RefineExistsEq
import ProofAutomation.SimpGoal
import ProofAutomation.Z3Tactic
import ProofAutomation.Z3Local

open Lean Meta Elab Tactic

elab "simp_hyps" : tactic => simpHypsLoop
elab "simp_goal" : tactic => ProofAutomation.simpGoalLoop
elab "prove_axiom" : tactic => proveAxiomImpl
elab "search_axioms" h?:(ident)? : tactic => do
  match h? with
  | none => searchAxiomsImpl .all
  | some i =>
    let n := i.getId
    if n == `goal then searchAxiomsImpl .goalOnly
    else if n == `hyps then searchAxiomsImpl .hypsOnly
    else searchAxiomsImpl (.hypOnly n)
elab "propose_axiom" name:str hs:ident* : tactic => proposeAxiomImpl name hs
elab "propose_counterexample" outer:((colGt ident))? seed:((colGt num))? : tactic => do
  let name? : Option Name ← match outer with
    | some id => pure (some (← Lean.Elab.realizeGlobalConstNoOverloadWithInfo id))
    | none => pure none
  ProposeCounterexample.proposeCounterexampleImpl name? (seed.map (·.getNat))
