module

import all LeanProofReview.Arithmetic
import all LeanProofReview.FiniteSums
import all LeanProofReview.ReviewCases
public meta import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command

public meta section

open Lean Elab Command

/-- Inspect declarations by their defining module, including names outside the project namespace. -/
elab "#audit_project" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => modules[idx]!
      | none => env.mainModule
    unless owner == `LeanProofReview || (`LeanProofReview).isPrefixOf owner do
      continue
    match info with
    | .axiomInfo _ => throwError "Project axiom is forbidden: {name}"
    | .thmInfo _ =>
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless allowed.contains dependency do
          throwError "Axiom audit failed: {name} depends on {dependency}"
      logInfo m!"AUDIT {name}: {dependencies}"
      count := count + 1
    | _ => pure ()
  if count == 0 then
    throwError "Axiom audit found no project theorems"
  logInfo m!"Axiom audit passed for all {count} project theorem declarations."

#audit_project
