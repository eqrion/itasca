import Exec.Abs.BrTableStep
import Exec.Abs.Core.ChosenRun
import Exec.Abs.Cumulative.Progress
import Exec.Abs.Executable.ChosenRun
import Exec.Abs.Indirect.HostCorrect
import Exec.Abs.Ownership.Run
import Exec.Abs.Sim.ChosenNumeric
import Exec.Abs.Sim.ChosenTerminal
import Exec.Abs.SimdCumulative.Run
import Exec.Code.Body.Control.Table.CumulativeTablePoint
import Exec.Code.Body.Reader.Calls.ReaderIndirectCapacity
import Exec.Code.Body.Reader.Common.CumulativeReaderCompilerStateful
import Exec.Code.Body.Reader.Common.ReaderStatefulEmission
import Exec.Code.Body.Reader.Common.StatefulReaderPrefixGenericWasm1
import Exec.Code.Body.Reader.Control.ReaderScopedBranchWasm2
import Exec.Code.Body.Reader.Float.ReaderFloatConstantCapacity
import Exec.Code.Body.Reader.Memory.ReaderMemoryCapacity
import Exec.Code.Body.Reader.Memory.StructuredReaderCompilerMemorySizeWithTables
import Exec.Code.Body.Reader.Simd.ReaderSimdPureEmission
import Exec.Code.Body.Reader.Table.ReaderTableLayoutWasm1
import Exec.Code.Body.Reader.Table.ReaderTableLayoutWasm2
import Exec.Code.Body.Reader.Table.SourceTableExitSlots
import Exec.Code.Body.Reader.Table.SourceTableInstructionPrefix
import Exec.Code.Body.Reader.Table.TableReaderCompilerBodyWasm2
import Exec.Code.Body.Relations.Table.TableFunction
import Exec.Code.Local.Callbacks.Calls.ScopeCallbackStack
import Exec.Code.Local.Callbacks.Common.CloseBody
import Exec.Code.Local.Callbacks.Common.ClosePrefix
import Exec.Code.Local.Callbacks.Common.FixupSafety
import Exec.Code.Local.Callbacks.Control.CloseBlockCertificates
import Exec.Code.Local.Capacity.BranchTableCallbackBounds
import Exec.Code.Local.Capacity.CapacityDeterministic
import Exec.Code.Local.Capacity.CloseBlockAvailability
import Exec.Code.Local.Capacity.LowerTableGrowth
import Exec.Code.Local.Capacity.ScalarAuxiliaryGrowth
import Exec.Code.Local.Capacity.SimdConstantCapacity
import Exec.Code.Local.Capacity.SimdGrowth
import Exec.Code.Local.Capacity.SourceAvailability
import Exec.Code.Local.Capacity.TableSourceBudget
import Exec.Code.Local.Control.Control.StructuredCloseElsePrefix
import Exec.Code.Local.Control.Control.StructuredCloseIfPrefix
import Exec.Code.Local.Control.Table.StructuredCodeTableExtension
import Exec.Code.Local.Lowering.Simd.SimdIndirect
import Exec.Code.Local.Relations.Calls.BranchPrefixCallback
import Exec.Code.Local.Relations.Calls.ConditionalPrefixCallback
import Exec.Code.Local.Relations.Calls.LoopPrefixCallback
import Exec.Code.Local.Relations.Common.SliceDeclared
import Exec.Code.Local.Relations.Control.DeadControl
import Exec.Code.Local.Relations.Table.BranchTableSelected
import Exec.Code.Module.CompilePreparedTotal
import Exec.Code.Module.EntryHeaderAvailable
import Exec.Code.Module.SourceAllocationDemand
import Exec.Examples.Host.AllocationCallbackExamples
import Exec.Examples.Host.OpenChosenExamples
import Exec.Examples.Host.OpenReentrantExamples
import Exec.Interp.Calls.CallStep
import Exec.Interp.Control.BranchCertified
import Exec.Interp.Core.ControlExecution
import Exec.Interp.Core.LocalExecution
import Exec.Interp.FloatCore.LocalGet
import Exec.Interp.FloatCore.LocalWrite
import Exec.Interp.Invocation.OpenInvokeFootprint
import Exec.Interp.Machines.Core.CoreCallExecution
import Exec.Interp.Machines.Core.CoreEpilogueExecution
import Exec.Interp.Machines.Core.CoreFloatConstantExecution
import Exec.Interp.Machines.Core.CoreIntegerConstantExecution
import Exec.Interp.Machines.Core.CoreReturnExecution
import Exec.Interp.Machines.Core.CoreSelectExecution
import Exec.Interp.Machines.Slice.SliceInfinite
import Exec.Interp.Memory.MemoryCoreExecution
import Exec.Interp.Relations.CertifiedStep
import Exec.Interp.Simd.Common.SimdAllTrueExecute
import Exec.Interp.Simd.Common.SimdAverageExecute
import Exec.Interp.Simd.Common.SimdBitmaskExecute
import Exec.Interp.Simd.Common.SimdCompareExecute
import Exec.Interp.Simd.Common.SimdExtendExecute
import Exec.Interp.Simd.Common.SimdPopcountExecute
import Exec.Interp.Simd.Common.SimdShiftExecute
import Exec.Interp.Simd.Common.SimdTruncSatExecute
import Exec.Interp.Simd.Common.SimdUnaryExecute
import Exec.Interp.Simd.Float.SimdCompareFloatExecute
import Exec.Interp.Simd.Float.SimdFloatBinaryExecute
import Exec.Interp.Simd.Float.SimdFloatResizeExecute
import Exec.Interp.Simd.Float.SimdFloatUnaryExecute
import Exec.Interp.Simd.Integer.SimdConvertIntegerExecute
import Exec.Interp.Simd.Integer.SimdDotExecute
import Exec.Interp.Simd.Integer.SimdIntegerArithmeticExecute
import Exec.Interp.Simd.Integer.SimdIntegerMinMaxExecute
import Exec.Interp.Simd.Integer.SimdIntegerSaturatingExecute
import Exec.Interp.Simd.Integer.SimdNarrowExecute
import Exec.Interp.Simd.Integer.SimdPairwiseExecute
import Exec.Interp.Simd.Integer.SimdQ15Execute
import Exec.Interp.Simd.Integer.SimdWidenExecute
import Exec.Interp.Simd.Memory.SimdMemoryExtendExecute
import Exec.Interp.Simd.Memory.SimdMemoryLaneExecute
import Exec.Interp.Simd.Memory.SimdMemoryLaneStoreExecute
import Exec.Interp.Simd.Memory.SimdMemoryLoadExecute
import Exec.Interp.Simd.Memory.SimdMemorySplatExecute
import Exec.Interp.Simd.Memory.SimdMemoryStoreExecute
import Exec.Interp.Simd.Memory.SimdMemoryZeroExecute
import Exec.Interp.StructuredMachine.ConstantUniform
import Exec.Interp.StructuredMachine.JumpUniform
import Exec.Spec.Choices.PackedReadDeterminism
import Exec.Spec.ModuleMembership
import Exec.Spec.Open.ExecutionScheduleOutcomes
import Exec.Spec.Open.WasmBoundarySuffix
import Exec.Spec.TableBounds
import Exec.Store.Api.ApiGrowSourceCauses
import Exec.Store.Api.ApiGrowthExtension
import Exec.Store.Api.CopyTypeAvailability
import Exec.Store.Initialization.DataCountLoop
import Exec.Store.Initialization.ElementTypeLoop
import Exec.Store.Initialization.PrecheckCertifiedErrors
import Exec.Store.Initialization.SegmentInitializeBounds
import Exec.Store.Instantiation.InstantiateNoStartCode
import Exec.Store.Instantiation.InstantiateReady
import Exec.Store.Instantiation.InstantiateRollback
import Exec.Store.Instantiation.InstantiateWasm1Bounds
import Exec.Store.Invariant.CompiledHost
import Exec.Store.Invariant.CoreCompiledHost
import Exec.Store.Invariant.ReserveMapCauses
import Exec.Store.Preparation.AllocationSourceCounts
import Exec.Store.Preparation.PreparationOwnedMaps
import Exec.Store.Preparation.PreparationTableTypes
import Exec.Store.Preparation.StagingComplete
import Exec.Theorems.Api.CertifiedApiHost
import Exec.Theorems.Api.CertifiedApiIssued
import Exec.Theorems.Api.CertifiedApiMemoryBorrow
import Exec.Theorems.Api.CertifiedIssuedApi
import Exec.Theorems.Api.CertifiedMemoryWrite
import Exec.Theorems.Api.ExecutableInvDefinitionResults
import Exec.Theorems.Api.ExecutableInvIssued
import Exec.Theorems.Api.ExecutableInvMemoryBorrow
import Exec.Theorems.Api.ExecutableInvReadResults
import Exec.Theorems.Api.MemoryGrowInstructionCertified
import Exec.Theorems.Api.SupportedApiIssued
import Exec.Theorems.Api.SupportedApiMemoryWrite
import Exec.Theorems.Api.SupportedApiReads
import Exec.Theorems.Api.TableGrowInstructionCertified
import Exec.Theorems.Composition.Certified.CertifiedCoreFloat
import Exec.Theorems.Composition.Certified.CertifiedSliceReferences
import Exec.Theorems.Composition.Certified.CertifiedSourceResources
import Exec.Theorems.Composition.Certified.CertifiedSourceValues
import Exec.Theorems.Composition.Core.CoreGlobalInstructionCertified
import Exec.Theorems.Composition.Executable.ExecutableEventfulLoop
import Exec.Theorems.Composition.Executable.ExecutableEventfulResults
import Exec.Theorems.Composition.MemoryCopyInstructionCertified
import Exec.Theorems.Composition.MemoryFillInstructionCertified
import Exec.Theorems.Composition.MemoryInstructionCertified
import Exec.Theorems.Composition.MemorySizeInstructionCertified
import Exec.Theorems.Composition.NewCertifiedCore
import Exec.Theorems.Composition.NewCertifiedCumulative
import Exec.Theorems.Composition.NewCertifiedFloatCore
import Exec.Theorems.Composition.NewCertifiedSlice
import Exec.Theorems.Composition.ReturnedExecutableActions
import Exec.Theorems.Composition.SegmentDropInstructionCertified
import Exec.Theorems.Composition.SegmentInitInstructionCertified
import Exec.Theorems.Composition.Supported.ChosenLoopResources
import Exec.Theorems.Composition.Supported.ChosenNativeCompletion
import Exec.Theorems.Composition.TableCopyInstructionCertified
import Exec.Theorems.Composition.TableFillInstructionCertified
import Exec.Theorems.Composition.World.ChosenWorldErasure
import Exec.Theorems.Composition.World.ChosenWorldResultErasure
import Exec.Theorems.Host.Callbacks.HostCorrespondence
import Exec.Theorems.Host.Chosen.PureSourcePolicy
import Exec.Theorems.Host.HostDirectRecording
import Exec.Theorems.Host.HostDirectRecordingInvariant
import Exec.Theorems.Host.HostIndirectDispatch
import Exec.Theorems.Host.HostIndirectRecording
import Exec.Theorems.Host.HostIndirectStepRecording
import Exec.Theorems.Host.Open.Completeness.ChosenSourceCompleteness
import Exec.Theorems.Host.Open.Completeness.ReferenceHostPrefix
import Exec.Theorems.Host.Open.Completeness.ReturningRecovery
import Exec.Theorems.Host.Open.Driver.IndirectTrapPrefix
import Exec.Theorems.Host.Open.Driver.InvocationPrefixes
import Exec.Theorems.Host.Open.Driver.LocalPrefix
import Exec.Theorems.Host.Open.Driver.TypedResumption
import Exec.Theorems.Host.Open.Driver.WasmLoop
import Exec.Theorems.Host.Open.Erasure.EraseRun
import Exec.Theorems.Host.Open.Native.FiniteNative
import Exec.Theorems.Host.Open.Native.NativeSourceInvocation
import Exec.Theorems.Host.Open.Source.State.DivergentPrefixes
import Exec.Theorems.Host.Open.Source.State.Entry
import Exec.Theorems.Host.Reentrant.RankedHostInvocation
import Exec.Theorems.Host.Reentrant.RetainedFunctionScope
import Exec.Theorems.Host.Reentrant.ScopedFiniteCallbacks
import Exec.Theorems.Instantiation.InstantiateCapacities
import Exec.Theorems.Instantiation.InstantiateCertifiedCore
import Exec.Theorems.Instantiation.InstantiateCertifiedCumulative
import Exec.Theorems.Instantiation.InstantiateCertifiedExecutable
import Exec.Theorems.Instantiation.InstantiateCertifiedFloatCore
import Exec.Theorems.Instantiation.InstantiateCoreDivergence
import Exec.Theorems.Instantiation.InstantiateCoreSourceDivergence
import Exec.Theorems.Instantiation.InstantiateCoreSourceInfinite
import Exec.Theorems.Instantiation.InstantiateCumulativeSourceDivergence
import Exec.Theorems.Instantiation.InstantiateCumulativeSourceInfinite
import Exec.Theorems.Instantiation.InstantiateExecutableEventfulCompiled
import Exec.Theorems.Instantiation.InstantiateExecutableEventfulInfinite
import Exec.Theorems.Instantiation.InstantiateExecutableEventfulNoLink
import Exec.Theorems.Instantiation.InstantiateExecutableEventfulResources
import Exec.Theorems.Instantiation.InstantiateExecutableEventfulWorld
import Exec.Theorems.Instantiation.InstantiateExecutableInv
import Exec.Theorems.Instantiation.InstantiateExecutableNoLink
import Exec.Theorems.Instantiation.InstantiateExecutableRecordedCompiled
import Exec.Theorems.Instantiation.InstantiateExecutableResources
import Exec.Theorems.Instantiation.InstantiateExecutableSourceDivergence
import Exec.Theorems.Instantiation.InstantiateExecutableSourceInfinite
import Exec.Theorems.Instantiation.InstantiateExecutableWorldInfinite
import Exec.Theorems.Instantiation.InstantiateExecutableWorldNoLink
import Exec.Theorems.Instantiation.InstantiateExecutableWorldRecordingResources
import Exec.Theorems.Instantiation.InstantiateFloatCoreSourceDivergence
import Exec.Theorems.Instantiation.InstantiateFloatCoreSourceInfinite
import Exec.Theorems.Instantiation.InstantiateSourceDivergence
import Exec.Theorems.Invocation.InvokeCoreChecked
import Exec.Theorems.Invocation.InvokeCumulativeChecked
import Exec.Theorems.Invocation.InvokeEventfulDivergence
import Exec.Theorems.Invocation.InvokeExecutableApiTyped
import Exec.Theorems.Invocation.InvokeExecutableBoundaries
import Exec.Theorems.Invocation.InvokeExecutableEventfulChecked
import Exec.Theorems.Invocation.InvokeFloatCoreChecked
import Exec.Theorems.Invocation.InvokeHostChecked
import Exec.Theorems.Invocation.InvokeSliceReferenceTypedOutcomes
import Exec.Theorems.Invocation.PublicExecutableEventfulDivergence
import Exec.Theorems.Invocation.PublicExecutableEventfulResources
import Exec.Theorems.Invocation.PublicExecutableEventfulResults
import Exec.Theorems.Invocation.PublicExecutableEventfulTyped
import Exec.Theorems.Invocation.PublicExecutableFinite
import Exec.Theorems.Invocation.PublicExecutableInvInvocation
import Exec.Theorems.Invocation.PublicExecutableRecorded
import Exec.Theorems.Invocation.PublicExecutableResources
import Exec.Theorems.Invocation.PublicExecutableSafety
import Exec.Theorems.Invocation.PublicExecutableWorldChosen
import Exec.Theorems.Invocation.PublicExecutableWorldFinite
import Exec.Theorems.Invocation.PublicExecutableWorldTyped
import Exec.Theorems.Invocation.PublicInvariantChosenMatches
import Exec.Theorems.Invocation.PublicInvocationNoObjects
import Exec.Theorems.Invocation.PublicWorldChosenMatches
import Exec.Theorems.Invocation.PublicWorldChosenTermination
import Exec.Theorems.Progress.CoreFinite
import Exec.Theorems.Progress.CumulativeFinite
import Exec.Theorems.Progress.ExecutableRecordedInfinite
import Exec.Theorems.Progress.ExecutableWorldRecordedInfinite
import Exec.Theorems.Progress.FloatCoreFinite
import Exec.Theorems.Progress.SupportedFinite
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

