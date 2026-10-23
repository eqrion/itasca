import Exec.Code.Local.Capacity.LowerTableGrowth
import Exec.Examples.Host.AllocationCallbackExamples
import Exec.Examples.Host.OpenChosenExamples
import Exec.Examples.Host.OpenReentrantExamples
import Exec.Spec.ModuleMembership
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Axiom audit

Checks that every declaration from an `Exec` module depends only on `propext`,
`Classical.choice` and `Quot.sound`, and fails the build otherwise. The import list is
generated: it names the sink modules of the import graph, so that every handwritten module is
reachable from this file. Set `EXEC_AUDIT_VERBOSE=1` to print the axioms of each declaration.
-/

-- Select by source module, not namespace or declaration kind. This includes
-- private proofs, definitions with proof fields, and external models declared
-- in Aeneas namespaces. Upstream declarations are checked through dependencies.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  -- In Lean 4.31 this accessor maps the entire module array. Compute it once,
  -- rather than once per declaration in the imported environment.
  let moduleNames := env.header.moduleNames
  -- Reporting is optional; declaration selection and axiom checks are not.
  let verbose := (← IO.getEnv "EXEC_AUDIT_VERBOSE") == some "1"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations ← env.constants.foldM (init := #[]) fun names n _ => do
    if let some idx := env.getModuleIdxFor? n then
      if (`Exec).isPrefixOf moduleNames[idx.toNat]! then
        return names.push n
    return names
  let declarations := if verbose then
    declarations.qsort (fun a b => a.toString < b.toString)
    else declarations
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless allowed.contains ax do
        throwError "{decl} depends on unapproved axiom {ax}"
    if verbose then
      logInfo m!"{decl}: {axioms}"
  logInfo m!"Audited {declarations.size} Exec declarations (all kinds and namespaces); only standard Lean logical axioms are allowed."

