import Itasca.Body.EndTyping
import Itasca.Examples.BrTableExamples
import Itasca.Examples.BrTableTraceExamples
import Itasca.Examples.CompletenessExamples
import Itasca.Examples.ModuleConsumerExamples
import Itasca.Examples.ModuleFunctionExamples
import Itasca.Examples.ModuleImportedGlobalExamples
import Itasca.Examples.ModuleNegativeExamples
import Itasca.Examples.ModuleSectionExamples
import Itasca.Examples.ModuleTraceExamples
import Itasca.Examples.StreamExamples
import Itasca.Examples.VisitorTraceExamples
import Itasca.Examples.WasmCompletenessBoundary
import Itasca.Module.ModuleCustomRanges
import Itasca.ModuleBinaryUnique
import Itasca.ModuleCompleteness
import Itasca.ModuleDecomposed
import Itasca.ModuleEntryTrace
import Itasca.ModuleEntryVisitor
import Itasca.ModuleValidation
import Itasca.Stream.StreamBatchBounds
import Itasca.StreamDriverComplete
import Itasca.StreamDriverTotal
import Itasca.StreamSlice
import Itasca.StreamSliceCompleteness
import Itasca.StreamValidation
import Itasca.VisitorBodyComplete
import Itasca.VisitorBodyErasure
import Itasca.VisitorBodyTrace
import Itasca.VisitorTraceCorollaries
import Itasca.Wasm1Soundness
import Itasca.WasmBinaryUnique
import Itasca.WasmComplete
import Itasca.WasmSoundness
import Lean.Elab.Command
import Lean.Util.CollectAxioms

-- Select by source module, not namespace or declaration kind. This includes
-- private proofs, definitions with proof fields, and external models declared
-- in Aeneas namespaces. Upstream declarations are checked through dependencies.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations ← env.constants.foldM (init := #[]) fun names n _ => do
    if let some idx := env.getModuleIdxFor? n then
      if (`Itasca).isPrefixOf env.header.moduleNames[idx.toNat]! then
        return names.push n
    return names
  let declarations := declarations.qsort (fun a b => a.toString < b.toString)
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless allowed.contains ax do
        throwError "{decl} depends on unapproved axiom {ax}"
    logInfo m!"{decl}: {axioms}"
  logInfo m!"Audited {declarations.size} Itasca declarations (all kinds and namespaces); only standard Lean logical axioms are allowed."
