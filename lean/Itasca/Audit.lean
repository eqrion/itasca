import Lean

/-! Axiom check for the project imports supplied by the Lake `audit` target. -/

open Lean

run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut usedAxioms : NameSet := {}
  for (declName, _) in env.constants.map₁ do
    let some index := env.getModuleIdxFor? declName | continue
    let mod := env.header.modules[index.toNat]!.module
    let root := mod.getRoot
    -- Check the generated specification through dependencies of project proofs.
    unless root == `Itasca || root == `ItascaRust ||
        (root == `WebAssembly && mod != `WebAssembly) do continue
    for axiomName in ← collectAxioms declName do
      unless allowed.contains axiomName do
        logError m!"{declName} depends on disallowed axiom {axiomName}"
      usedAxioms := usedAxioms.insert axiomName
  IO.println "Axioms used by Itasca, ItascaRust, and the WebAssembly extensions:"
  for axiomName in usedAxioms.toArray.qsort Name.lt do
    IO.println s!"  {axiomName}"
