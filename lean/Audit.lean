import Lean

/-! Axiom check for the project imports supplied by `just audit`. -/

open Lean

run_cmd do
  let env ← getEnv
  let mut projectDecls : NameSet := {}
  let mut dependencies : NameSet := {}
  let mut usedAxioms : NameSet := {}
  for (declName, info) in env.constants.map₁.toList do
    let some index := env.getModuleIdxFor? declName | continue
    let root := env.header.moduleNames[index.toNat]!.getRoot
    unless root == `Itasca || root == `SpecExt do continue
    projectDecls := projectDecls.insert declName
    let direct := info.getUsedConstantsAsSet
    if direct.contains ``sorryAx then
      logError m!"{declName} depends on sorryAx"
    dependencies := dependencies ++ direct
    if info matches .axiomInfo _ then
      usedAxioms := usedAxioms.insert declName
  -- Every project declaration was scanned above. Follow axioms transitively
  -- from each distinct imported dependency to include upstream proof bodies.
  for dep in dependencies do
    if projectDecls.contains dep then continue
    let used ← collectAxioms dep
    if dep != ``sorryAx && used.contains ``sorryAx then
      logError m!"Imported dependency {dep} depends on sorryAx"
    for axiomName in used do
      usedAxioms := usedAxioms.insert axiomName
  IO.println "Axioms used by Itasca and SpecExt:"
  for axiomName in usedAxioms.toArray.qsort Name.lt do
    IO.println s!"  {axiomName}"
