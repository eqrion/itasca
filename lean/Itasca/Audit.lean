import Itasca.Examples.DeclaredReferences
import Itasca.MultiValue.CallbackRefinement
import Itasca.MultiValue.CallbackBodyRefinement
import Itasca.MultiValue.CallbackControlBytes
import Itasca.MultiValue.CallbackTrace
import Itasca.MultiValue.CallbackBytesSimd
import Itasca.MultiValue.CallbackBytesDispatch
import Itasca.MultiValue.CallbackReturnBytes
import Itasca.MultiValue.CallbackStepTrace
import Itasca.MultiValue.CallbackCorrespondence
import Itasca.MultiValue.BlockDecode
import Itasca.Profile.BinaryUnique
import Itasca.MultiValue.Typing
import Itasca.MultiValue.Stack
import Itasca.MultiValue.Signature
import Itasca.MultiValue.BodyTotal
import Itasca.MultiValue.Invariant
import Itasca.MultiValue.Complete
import Itasca.MultiValue.Visitor
import Itasca.MultiValue.SuffixTyping
import Itasca.Binary.SignedLeb33
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
import Itasca.Examples.MultiValueGrammar
import Itasca.Examples.MultiValueBody
import Itasca.Examples.MultiValueModule
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
