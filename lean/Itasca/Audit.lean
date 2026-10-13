import Itasca.Body.EndTyping
import Itasca.Examples.BrTableExamples
import Itasca.Examples.BrTableTraceExamples
import Itasca.Examples.CompletenessExamples
import Itasca.Examples.DeclaredReferences
import Itasca.Examples.ModuleConsumerExamples
import Itasca.Examples.ModuleFunctionExamples
import Itasca.Examples.ModuleImportedGlobalExamples
import Itasca.Examples.ModuleNegativeExamples
import Itasca.Examples.ModuleSectionExamples
import Itasca.Examples.ModuleTraceExamples
import Itasca.Examples.MultiValueBody
import Itasca.Examples.MultiValueModule
import Itasca.Examples.StreamExamples
import Itasca.Examples.VisitorTraceExamples
import Itasca.Examples.WasmCompletenessBoundary
import Itasca.Generated.FunsExternal
import Itasca.Module.ModuleCustomRanges
import Itasca.Module.ModuleEntryTrace
import Itasca.MultiValue.CallbackCorrespondence
import Itasca.Profile.BinaryUnique
import Itasca.Stream.StreamBatchBounds
import Itasca.Visitor.VisitorTraceCorollaries
import Lean.Elab.Command
import Lean.Util.CollectAxioms

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
  let verbose := (← IO.getEnv "ITASCA_AUDIT_VERBOSE") == some "1"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations ← env.constants.foldM (init := #[]) fun names n _ => do
    if let some idx := env.getModuleIdxFor? n then
      if (`Itasca).isPrefixOf moduleNames[idx.toNat]! then
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
  logInfo m!"Audited {declarations.size} Itasca declarations (all kinds and namespaces); only standard Lean logical axioms are allowed."
