import Itasca.TypeTranslation
import Itasca.Nop
import Itasca.Branch
import Itasca.End
import Itasca.Numeric
import Itasca.Sequence
import Itasca.EndTyping
import Itasca.StackSemantics
import Itasca.CoreSimple
import Itasca.SignedLeb
import Itasca.SignedConst
import Itasca.Frames
import Itasca.CoreSyntax
import Itasca.CoreBinary
import Itasca.CoreBranch
import Itasca.CoreVisitor
import Itasca.Body
import Itasca.CoreInvariant
import Itasca.CoreBody
import Itasca.CoreStepBranch
import Itasca.CoreSoundness
import Itasca.CoreExamples
import Itasca.WasmSoundness
import Itasca.VisitorBodyErasure
import Itasca.WasmScalarExamples
import Itasca.BrTableExamples
import Itasca.WasmExamples
import Itasca.WasmComplete
import Itasca.WasmCompletenessBoundary
import Itasca.CompletenessExamples
import Itasca.VisitorComplete
import Itasca.VisitorBodyComplete
import Itasca.VisitorBodyTrace
import Itasca.VisitorTraceCorollaries
import Itasca.VisitorTraceExamples
import Itasca.BrTableTraceExamples
import Itasca.SpecChecks
import Itasca.ModuleBinary
import Itasca.ModuleCopies
import Itasca.ModuleTranslation
import Itasca.BodyContext
import Itasca.ModulePipeline
import Itasca.ModuleExternals
import Itasca.ModuleDataTyping
import Itasca.ModuleTail
import Itasca.ModuleEnv
import Itasca.ModuleDeclarations
import Itasca.ModuleHeader
import Itasca.ModuleCodeEntry
import Itasca.ModuleValidation
import Itasca.ModuleCompleteness
import Itasca.ModuleDecomposed
import Itasca.ModuleCodeTotal
import Itasca.ModuleCustomVisitor
import Itasca.ModuleVisitorValidation
import Itasca.ModuleVisitorTransfer
import Itasca.ModuleDeferredValidation
import Itasca.ModuleEntryOrder
import Itasca.ModuleTraceValidation
import Itasca.ModuleCustomRanges
import Itasca.ModuleTraceExamples
import Itasca.ModuleEntryTrace
import Itasca.ModuleSectionExamples
import Itasca.ModuleFunctionExamples
import Itasca.ModuleNegativeExamples
import Itasca.ModuleConsumerExamples
import Itasca.ModuleImportedGlobalExamples
import Itasca.ModuleExamples
import Itasca.ModuleUnicodeExamples
import Lean.Util.CollectAxioms
import Lean.Elab.Command

-- The imported SpecTec file contains unfinished upstream lemmas. No Itasca
-- theorem may depend on those or on a domain axiom. Discover public theorems
-- automatically so a newly exported proof cannot silently miss this audit.
-- Private helpers are checked transitively through their public callers.
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations ← (← getEnv).constants.foldM (init := #[]) fun names n info => do
    if (`Itasca).isPrefixOf n && info.isTheorem then
      return names.push n
    return names
  let declarations := declarations.qsort (fun a b => a.toString < b.toString)
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless allowed.contains ax do
        throwError "{decl} depends on unapproved axiom {ax}"
    logInfo m!"{decl}: {axioms}"
  -- These maps contain proof fields as well as data. Audit every row directly,
  -- including rows not singled out by a concrete regression example.
  for decl in #[``Itasca.Numeric.opcodeMeaning, ``Itasca.MemoryMeaning.opcodeMeaning,
      ``Itasca.ScalarConst.floatValue, ``Itasca.EnvTranslation.context,
      ``Itasca.Wasm.Validated, ``Itasca.Wasm1.Body,
      ``Itasca.Wasm1.Environment, ``Itasca.Wasm1.Instructions,
      ``Itasca.ModuleBinary.ModuleEncodingWithinLimits, ``Itasca.ModuleBinary.CodeEncodingWithinLimits,
      ``Itasca.ModuleBinary.ModuleEncoding, ``Itasca.ModuleElaboration.moduleOf,
      ``Itasca.ModuleElaboration.Elaborates, ``Itasca.ModuleElaboration.Profile,
      ``Itasca.ModuleElaboration.contextOf, ``Itasca.ModuleElaboration.Matches,
      ``Itasca.ModuleElaboration.AccessorTypes, ``Itasca.ModuleSound.Validated,
      ``Itasca.CodeEntry.Typed, ``Itasca.CodeEntry.AcceptedTrace,
      ``Itasca.ModuleCode.HooksTotal, ``Itasca.ModuleCode.VisitorContract,
      ``Itasca.ModuleCodeVisitor.Accepts, ``Itasca.ModuleCodeVisitor.Validates,
      ``Itasca.ModuleCodeVisitor.Records, ``Itasca.ModuleCodeVisitor.EntriesValidate,
      ``Itasca.ModuleCodeVisitor.recorder, ``Itasca.ModuleTail.Preserves,
      ``Itasca.ModuleTrace.CustomAt, ``Itasca.ModuleTrace.SectionTrace,
      ``Itasca.ModuleTrace.CodeEntriesTrace, ``Itasca.ModuleTrace.CodeTrace,
      ``Itasca.ModuleTrace.Accepted, ``Itasca.ModuleTrace.RecordsCustom,
      ``Itasca.ModuleTrace.RecordsCode, ``Itasca.ModuleTrace.entries,
      ``Itasca.ModuleTrace.customRecorder, ``Itasca.ModuleTrace.codeRecorder,
      ``Itasca.ModuleTrace.validatingRecorder,
      ``Itasca.FullVisitor.Accepts,
      ``Itasca.VisitorTrace.invoke, ``Itasca.VisitorTrace.ofHandler,
      ``Itasca.VisitorTrace.NumericHook.opcode, ``Itasca.VisitorTrace.NumericHook.instruction,
      ``Itasca.VisitorTrace.MemoryHook.opcode, ``Itasca.VisitorTrace.MemoryHook.instruction,
      ``Itasca.VisitorTrace.Action.token, ``Itasca.VisitorTrace.Action.opcode,
      ``Itasca.VisitorTrace.Records, ``Itasca.VisitorTrace.instrument,
      ``Itasca.VisitorTrace.recorder, ``Itasca.VisitorTrace.rejectAt,
      ``Itasca.VisitorTrace.BodyTrace, ``Itasca.VisitorTrace.AcceptedBody,
      ``Itasca.VisitorTrace.project] do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless allowed.contains ax do
        throwError "{decl} depends on unapproved axiom {ax}"
    logInfo m!"Adapter {decl}: {axioms}"
  logInfo m!"Audited {declarations.size} Itasca theorem declarations (including generated auxiliaries); only standard Lean logical axioms are allowed."
