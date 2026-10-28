import Exec.Theorems.Composition.Supported.SupportedBranchTableExecution
import Exec.Theorems.Composition.Supported.SupportedExecutionOutcome
import Exec.Theorems.Composition.StoreMutationFacts
import Exec.Interp.StructuredMachine.GlobalMutation
import Exec.Interp.StructuredMachine.SupportedHeadCoverage
import Exec.Interp.StructuredMachine.OrdinaryAdvance
import Exec.Interp.StructuredMachine.NumericExecutionOwned
import Exec.Interp.StructuredMachine.GlobalExecutionOwned
import Exec.Interp.StructuredMachine.FloatConstantExecutionOwned
import Exec.Interp.StructuredMachine.SelectExecutionOwned
import Exec.Interp.StructuredMachine.MemoryExecutionOwned
import Exec.Interp.StructuredMachine.CallExecution
import Exec.Interp.StructuredMachine.ReturnExecution
import Exec.Interp.StructuredMachine.UnreachableExecution
import Exec.Abs.Cumulative.Step
import Exec.Code.Local.Relations.Common.StatefulEmission
import Exec.Interp.Relations.CompiledFunctions
import Exec.Code.Local.Control.Common.CumulativeFunctionContext
import Exec.Interp.StructuredMachine.CompiledFunctions
import Exec.Code.Body.Control.Table.CumulativeTableExclusion
import Exec.Code.Local.Control.Common.Structured
import Exec.Code.Local.Control.Common.StructuredComposition
import Exec.Code.Local.Control.Table.StructuredCodePoint
import Exec.Interp.StructuredMachine.SupportedControlSemantics
import Exec.Interp.StructuredMachine.SupportedBoundarySemantics
import Exec.Theorems.Composition.Supported.SupportedScalarExecution
import Exec.Theorems.Composition.Supported.SupportedStatefulExecution
import Exec.Theorems.Composition.Supported.SupportedIndirectExecution
import Exec.Code.Local.Relations.Common.ScalarEmission
import Exec.Code.Local.Control.Common.StructuredLabels
import Exec.Interp.Control.StructuredPoint
import Exec.Abs.ModuleBindingsExtension
import Exec.Interp.Relations.SuspendedPoint
import Exec.Interp.Relations.FrameStoreMetadata
import Exec.Interp.Machines.Slice.SliceExecution
import Exec.Abs.Core.Typing
import Exec.Abs.Core
import Exec.Abs.Ownership.Core
import Exec.Interp.Core.Mutation
import Exec.Interp.Relations.SourceCallCause
import Exec.Interp.State.GlobalMutationStep
import Exec.Interp.Control.PendingJump
import Exec.Interp.Relations.ReferenceTransfers
import Exec.Interp.Relations.SourceClosure
import Exec.Interp.Core.Linear
import Exec.Interp.Relations.PrefixDispatch
import Exec.Abs.Core.Correct
import Exec.Interp.Relations.ControlPoint
import Exec.Interp.Numeric.Integer.NumericFetch
import Exec.Interp.Numeric.Integer.NumericCodePoint
import Exec.Abs.Numeric.TransitionSimulation
import Exec.Abs.Core.Bound
import Exec.Code.Local.Control.Table.StructuredCodeTableExclusion
import Exec.Interp.StructuredMachine.Execution
import Exec.Interp.StructuredMachine.OrdinaryExecution
import Exec.Interp.StructuredMachine.OrdinaryStack
import Exec.Interp.StructuredMachine.StackPreservation
import Exec.Interp.Relations.StackPreservation
import Exec.Interp.Relations.PrefixEffect
import Exec.Interp.Control.SkipStack
import Exec.Abs.Core.Step
import Exec.Abs.Numeric.Effect
import Exec.Abs.StepSafety
import Exec.Abs.Core.Pure
import Exec.Spec.Extend
import Exec.Interp.Core.OwnershipClosure
import Exec.Interp.Core.LocalInversion
import Exec.Interp.Relations.LocalCodePoint
import Exec.Interp.Relations.Fetch
import Exec.Interp.Relations.ValueLookup
import Exec.Interp.Relations.LocalCapacity
import Exec.Interp.Relations.Capacity
import Exec.Interp.Core.LocalPrefix
import Exec.Interp.Machines.Core.CoreOwnership
import Exec.Interp.Core.BoundClosure
import Exec.Abs.Numeric.Decode
import Exec.Interp.Control.BranchNoCopy
import Exec.Interp.Control.BranchConditionStep
import Exec.Interp.Relations.TypedOperands
import Exec.Interp.Relations.ControlEntry
import Exec.Interp.Control.LoopHead
import Exec.Interp.Machines.Core.CoreIntegerConstantPoint
import Exec.Interp.Machines.Core.CoreIntegerConstantSlots
import Exec.Interp.Machines.Slice.SliceOpcode
import Exec.Interp.State.GlobalCoreStep
import Exec.Interp.State.GlobalCoreOperands
import Exec.Code.Local.Capacity.GlobalCapacity
import Exec.Interp.Machines.Core.CoreFloatConstantPoint
import Exec.Interp.Machines.Core.CoreFloatConstantSlots
import Exec.Interp.Relations.SelectSlots
import Exec.Interp.Machines.Core.CoreSelectOperands
import Exec.Interp.Memory.MemoryCoreTransition
import Exec.Interp.Memory.MemoryCoreOperandBounds
import Exec.Interp.Memory.MemoryCoreEmission
import Exec.Interp.Memory.MemoryCoreStep
import Exec.Interp.Memory.MemoryCoreResult
import Exec.Interp.Memory.MemoryLoadStepFootprint
import Exec.Abs.Bound
import Exec.Abs.Numeric.Transition
import Exec.Abs.ReferenceBounds
import Exec.Interp.Machines.Core.CoreFunctionTyping
import Exec.Abs.CallSafety
import Exec.Interp.Calls.CallStack
import Exec.Code.Local.Relations.Common.CoreFunction
import Exec.Interp.Calls.CallRefinement
import Exec.Abs.Results
import Exec.Interp.Calls.ReturnRefinement
import Exec.Interp.Calls.ReturnResult
import Exec.Interp.Machines.Core.CoreUnreachableExecution
import Exec.Interp.Relations.StackRelation
import Exec.Interp.Relations.Epilogue
import Exec.Interp.Relations.Normalization
import Exec.Interp.Core.EmptyInversion
import Exec.Interp.Control.LabelCompletion
import Exec.Interp.Core.Erased
import Exec.Interp.Control.NormalizeClosure
import Exec.Interp.Control.NormalizeCompose
import Exec.Interp.Machines.Slice.SliceMeasure
import Exec.Store.Invariant.SemanticApi
import Exec.Store.Invariant.Syntax
import Exec.Spec.Mutation
import Exec.Interp.Memory.MemoryMutation
import Exec.Theorems.Composition.Core.CoreContents
import Exec.Representation.Collection
import Exec.Store.Invariant.FunctionTables
import Exec.Code.Local.Relations.Common.CoreFunctionContext
import Exec.Store.Invariant.CoreTypingExtension
import Exec.Store.Invariant.ObjectExtension
import Exec.Theorems.Composition.GlobalMutationShape
import Exec.Theorems.Composition.Core.CoreOwnership
import Exec.Store.Invariant.InstantiationCode
import Exec.Store.Initialization.SegmentObjectMetadata
import Exec.Theorems.Composition.Supported.SupportedSimdExecution
import Exec.Theorems.Composition.Supported.SupportedTypedSelectExecution
import Exec.Interp.StructuredMachine.EpilogueExecution
import Exec.Theorems.Composition.Supported.SupportedNormalizeOutcome
import Exec.Interp.StructuredMachine.NormalizeExecution
import Exec.Interp.StructuredMachine.PendingExecution
import Exec.Theorems.Composition.Supported.SupportedMeasure
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std Itasca.Runtime.Interp

/-- The fetched direct call is tied to its source opcode, not only to an
unindexed raw store boundary. -/
def DirectHostInstruction {M : Type} (store : runtime.store.Store M)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (op : instr) : Prop :=
  ∃ (index offset : U32) (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (host : U64),
    op=.CALL (.mk_uN index.val) ∧
    compiled.code.val[raw.pc.val]?=some (.Call index offset) ∧
    inst.funcs.val[index.val]?=some address ∧ store.funcs.val[address.index.val]?=some function ∧
    function.code=.Host host

/-- The normalized source point and concrete frame needed to discharge a host
boundary. All fields come from the existing execution invariant. -/
structure HostFrameSite {M : Type}
    (view : M → Slice U8) (code : Store.CodeInterpretation) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (expected : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) where
  index : Usize
  raw : runtime.interp.Frame
  inst : runtime.store.ModuleInst
  compiled : runtime.bytecode.CompiledFunction
  context : _root_.context
  targets : List Code.LabelTarget
  next : Nat
  output : List valtype
  last : index.val+1=exec.frames.length
  frameAt : exec.frames.val[index.val]?=some raw
  instanceAt : store.instances.val[raw.instance.val]?=some inst
  compiledAt : inst.module.functions.val[raw.function.val]?=some compiled
  program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes context.FUNCS
  slots : FrameSlots exec raw f
  moduleEq : f.module=Store.decodeInstance store inst
  point : StructuredMachine.FramePoint (Store.decodeStore view code store) raw f compiled context targets next output
  machine : StructuredMachine.Execution view code store exec
    ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ expected raw.pc.val false
  owned : Abs.Ownership.StateOwned (Store.ownershipBounds store)
    ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩

/-- Actual common dispatch yields one of these sites or an ordinary checked
step. Source-only normalization is retained for the later eventful join. -/
inductive StructuredHostSite {M : Type}
    (view : M → Slice U8) (code : Store.CodeInterpretation) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (expected : List valtype) : Nat → Bool → Abs.AState → Prop where
  | ready {ambient : frame} {f : Abs.AFrame} {rest : List Abs.AFrame} {op : instr} {after : List instr}
      (site : HostFrameSite view code exec store expected ambient {f with code:=op::after} rest)
      (kind : DirectHostInstruction store site.raw site.inst site.compiled op ∨
        ∃ table type : U32, op=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val) ∧
          SourceIndirectHostBoundary store ⟨Store.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩) :
      StructuredHostSite view code exec store expected site.raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩
  | normalize {count pc s ambient before after rest}
      (chain : ErasedSteps count before after)
      (site : StructuredHostSite view code exec store expected pc false ⟨s,ambient,after::rest,[]⟩) :
      StructuredHostSite view code exec store expected pc false ⟨s,ambient,before::rest,[]⟩
end Itasca.Runtime.Theorems
