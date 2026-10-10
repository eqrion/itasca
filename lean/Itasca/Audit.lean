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
import Itasca.ModuleCustomVisitor
import Itasca.ModuleCustomRanges
import Itasca.ModuleCustomTrace
import Itasca.ModuleTraceRecorders
import Itasca.ModuleTraceExamples
import Itasca.ModuleEntryTrace
import Itasca.ModuleSectionExamples
import Itasca.ModuleFunctionExamples
import Itasca.ModuleNegativeExamples
import Itasca.ModuleConsumerExamples
import Itasca.ModuleImportedGlobalExamples
import Itasca.ModuleExamples
import Itasca.ModuleUnicodeExamples
import Itasca.StreamSource
import Itasca.StreamSliceComplete
import Itasca.StreamHeaderComplete
import Itasca.StreamBatchSound
import Itasca.StreamBatchBounds
import Itasca.StreamBatchComplete
import Itasca.StreamDrain
import Itasca.StreamPartition
import Itasca.StreamSync
import Itasca.StreamRun
import Itasca.StreamSlice
import Itasca.StreamValidation
import Itasca.StreamCompleteRegions
import Itasca.StreamBatchFramingComplete
import Itasca.StreamSyncComplete
import Itasca.StreamSubmissionComplete
import Itasca.StreamExamples
import Itasca.StreamSliceCompleteness
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
      ``Itasca.ModuleCode.Extent, ``Itasca.ModuleCode.Section,
      ``Itasca.ModuleCode.EntryAt, ``Itasca.ModuleCode.EntriesTyped,
      ``Itasca.ModuleCode.Encoding, ``Itasca.ModuleCode.Validated, ``Itasca.ModuleCode.AbsentAt,
      ``Itasca.ModuleLayout.CodeAt, ``Itasca.ModuleLayout.Layout,
      ``Itasca.StreamSource.Coherent, ``Itasca.StreamSource.Available,
      ``Itasca.StreamSource.CallbacksTotal, ``Itasca.StreamSource.LenPost,
      ``Itasca.StreamSource.CanonicalAvailable,
      ``Itasca.stream.SliceSource.Insts.ItascaStreamSource,
      ``Itasca.StreamFraming.EntryFrame, ``Itasca.StreamFraming.HeaderChecked,
      ``Itasca.StreamFraming.HeaderAt, ``Itasca.StreamFraming.BatchInvariant,
      ``Itasca.StreamFraming.FrameStep, ``Itasca.StreamFraming.BatchStepPost,
      ``Itasca.StreamFraming.EntryFrames, ``Itasca.StreamFraming.BatchPost, ``Itasca.StreamSync.Tracks,
      ``Itasca.StreamScheduler.Partition,
      ``Itasca.StreamSubmission.Invariant, ``Itasca.StreamSubmission.Post,
      ``Itasca.StreamSubmission.SoundInvariant, ``Itasca.StreamSubmission.SoundPost,
      ``Itasca.StreamSubmission.CompleteInvariant, ``Itasca.StreamSubmission.CompletePost,
      ``Itasca.StreamCompleteRegions.Split, ``Itasca.StreamCompleteRegions.Certificate,
      ``Itasca.StreamAcceptingScheduler.Valid, ``Itasca.StreamAcceptingScheduler.ValidQueue,
      ``Itasca.StreamAcceptingScheduler.Accepts, ``Itasca.StreamSync.Queued,
      ``Itasca.StreamExamples.bytes, ``Itasca.StreamExamples.emptyEnv,
      ``Itasca.StreamExamples.emptyBytes, ``Itasca.StreamExamples.impossibleIssued,
      ``Itasca.StreamExamples.forgedBatch, ``Itasca.StreamExamples.incoherentSource,
      ``Itasca.ModuleConsumerExamples.badIssued, ``Itasca.ModuleConsumerExamples.observeCustoms,
      ``Itasca.StreamRun.Remaining, ``Itasca.StreamRun.Accepted,
      ``Itasca.ModuleTail.PreservesInvariant,
      ``Itasca.StreamRetirement.PollTotal, ``Itasca.StreamRetirement.SearchPost,
      ``Itasca.StreamRetirement.Retired, ``Itasca.StreamScheduler.CallbacksTotal,
      ``Itasca.StreamScheduler.Provenance, ``Itasca.StreamScheduler.Completed,
      ``Itasca.StreamBatch.Issued.seed, ``Itasca.StreamBatch.Issued.Bounded,
      ``Itasca.StreamBatch.Reachable, ``Itasca.StreamBatch.Prefix, ``Itasca.StreamBatch.Identity,
      ``Itasca.CodeEntry.Typed, ``Itasca.CodeEntry.AcceptedTrace,
      ``Itasca.ModuleTail.Preserves,
      ``Itasca.ModuleTrace.CustomAt, ``Itasca.ModuleTrace.SectionTrace,
      ``Itasca.ModuleTrace.RecordsCustom, ``Itasca.ModuleTrace.customRecorder,
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
