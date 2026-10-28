import Itasca.Runtime.Theorems.Composition.Supported.SupportedBranchTableExecution
import Itasca.Runtime.Theorems.Composition.Supported.SupportedExecutionOutcome
import Itasca.Runtime.Theorems.Composition.StoreMutationFacts
import Itasca.Runtime.Interp.StructuredMachine.GlobalMutation
import Itasca.Runtime.Interp.StructuredMachine.SupportedHeadCoverage
import Itasca.Runtime.Interp.StructuredMachine.OrdinaryAdvance
import Itasca.Runtime.Interp.StructuredMachine.NumericExecutionOwned
import Itasca.Runtime.Interp.StructuredMachine.GlobalExecutionOwned
import Itasca.Runtime.Interp.StructuredMachine.FloatConstantExecutionOwned
import Itasca.Runtime.Interp.StructuredMachine.SelectExecutionOwned
import Itasca.Runtime.Interp.StructuredMachine.MemoryExecutionOwned
import Itasca.Runtime.Interp.StructuredMachine.CallExecution
import Itasca.Runtime.Interp.StructuredMachine.ReturnExecution
import Itasca.Runtime.Interp.StructuredMachine.UnreachableExecution
import Itasca.Runtime.Abs.Cumulative.Step
import Itasca.Runtime.Code.Local.Relations.Common.StatefulEmission
import Itasca.Runtime.Interp.Relations.CompiledFunctions
import Itasca.Runtime.Code.Local.Control.Common.CumulativeFunctionContext
import Itasca.Runtime.Interp.StructuredMachine.CompiledFunctions
import Itasca.Runtime.Code.Body.Control.Table.CumulativeTableExclusion
import Itasca.Runtime.Code.Local.Control.Common.Structured
import Itasca.Runtime.Code.Local.Control.Common.StructuredComposition
import Itasca.Runtime.Code.Local.Control.Table.StructuredCodePoint
import Itasca.Runtime.Interp.StructuredMachine.SupportedControlSemantics
import Itasca.Runtime.Interp.StructuredMachine.SupportedBoundarySemantics
import Itasca.Runtime.Theorems.Composition.Supported.SupportedScalarExecution
import Itasca.Runtime.Theorems.Composition.Supported.SupportedStatefulExecution
import Itasca.Runtime.Theorems.Composition.Supported.SupportedIndirectExecution
import Itasca.Runtime.Code.Local.Relations.Common.ScalarEmission
import Itasca.Runtime.Code.Local.Control.Common.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.Abs.ModuleBindingsExtension
import Itasca.Runtime.Interp.Relations.SuspendedPoint
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Interp.Machines.Slice.SliceExecution
import Itasca.Runtime.Abs.Core.Typing
import Itasca.Runtime.Abs.Core
import Itasca.Runtime.Abs.Ownership.Core
import Itasca.Runtime.Interp.Core.Mutation
import Itasca.Runtime.Interp.Relations.SourceCallCause
import Itasca.Runtime.Interp.State.GlobalMutationStep
import Itasca.Runtime.Interp.Control.PendingJump
import Itasca.Runtime.Interp.Relations.ReferenceTransfers
import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Interp.Core.Linear
import Itasca.Runtime.Interp.Relations.PrefixDispatch
import Itasca.Runtime.Abs.Core.Correct
import Itasca.Runtime.Interp.Relations.ControlPoint
import Itasca.Runtime.Interp.Numeric.Integer.NumericFetch
import Itasca.Runtime.Interp.Numeric.Integer.NumericCodePoint
import Itasca.Runtime.Abs.Numeric.TransitionSimulation
import Itasca.Runtime.Abs.Core.Bound
import Itasca.Runtime.Code.Local.Control.Table.StructuredCodeTableExclusion
import Itasca.Runtime.Interp.StructuredMachine.Execution
import Itasca.Runtime.Interp.StructuredMachine.OrdinaryExecution
import Itasca.Runtime.Interp.StructuredMachine.OrdinaryStack
import Itasca.Runtime.Interp.StructuredMachine.StackPreservation
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.Interp.Relations.PrefixEffect
import Itasca.Runtime.Interp.Control.SkipStack
import Itasca.Runtime.Abs.Core.Step
import Itasca.Runtime.Abs.Numeric.Effect
import Itasca.Runtime.Abs.StepSafety
import Itasca.Runtime.Abs.Core.Pure
import Itasca.Runtime.Spec.Extend
import Itasca.Runtime.Interp.Core.OwnershipClosure
import Itasca.Runtime.Interp.Core.LocalInversion
import Itasca.Runtime.Interp.Relations.LocalCodePoint
import Itasca.Runtime.Interp.Relations.Fetch
import Itasca.Runtime.Interp.Relations.ValueLookup
import Itasca.Runtime.Interp.Relations.LocalCapacity
import Itasca.Runtime.Interp.Relations.Capacity
import Itasca.Runtime.Interp.Core.LocalPrefix
import Itasca.Runtime.Interp.Machines.Core.CoreOwnership
import Itasca.Runtime.Interp.Core.BoundClosure
import Itasca.Runtime.Abs.Numeric.Decode
import Itasca.Runtime.Interp.Control.BranchNoCopy
import Itasca.Runtime.Interp.Control.BranchConditionStep
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Interp.Relations.ControlEntry
import Itasca.Runtime.Interp.Control.LoopHead
import Itasca.Runtime.Interp.Machines.Core.CoreIntegerConstantPoint
import Itasca.Runtime.Interp.Machines.Core.CoreIntegerConstantSlots
import Itasca.Runtime.Interp.Machines.Slice.SliceOpcode
import Itasca.Runtime.Interp.State.GlobalCoreStep
import Itasca.Runtime.Interp.State.GlobalCoreOperands
import Itasca.Runtime.Code.Local.Capacity.GlobalCapacity
import Itasca.Runtime.Interp.Machines.Core.CoreFloatConstantPoint
import Itasca.Runtime.Interp.Machines.Core.CoreFloatConstantSlots
import Itasca.Runtime.Interp.Relations.SelectSlots
import Itasca.Runtime.Interp.Machines.Core.CoreSelectOperands
import Itasca.Runtime.Interp.Memory.MemoryCoreTransition
import Itasca.Runtime.Interp.Memory.MemoryCoreOperandBounds
import Itasca.Runtime.Interp.Memory.MemoryCoreEmission
import Itasca.Runtime.Interp.Memory.MemoryCoreStep
import Itasca.Runtime.Interp.Memory.MemoryCoreResult
import Itasca.Runtime.Interp.Memory.MemoryLoadStepFootprint
import Itasca.Runtime.Abs.Bound
import Itasca.Runtime.Abs.Numeric.Transition
import Itasca.Runtime.Abs.ReferenceBounds
import Itasca.Runtime.Interp.Machines.Core.CoreFunctionTyping
import Itasca.Runtime.Abs.CallSafety
import Itasca.Runtime.Interp.Calls.CallStack
import Itasca.Runtime.Code.Local.Relations.Common.CoreFunction
import Itasca.Runtime.Interp.Calls.CallRefinement
import Itasca.Runtime.Abs.Results
import Itasca.Runtime.Interp.Calls.ReturnRefinement
import Itasca.Runtime.Interp.Calls.ReturnResult
import Itasca.Runtime.Interp.Machines.Core.CoreUnreachableExecution
import Itasca.Runtime.Interp.Relations.StackRelation
import Itasca.Runtime.Interp.Relations.Epilogue
import Itasca.Runtime.Interp.Relations.Normalization
import Itasca.Runtime.Interp.Core.EmptyInversion
import Itasca.Runtime.Interp.Control.LabelCompletion
import Itasca.Runtime.Interp.Core.Erased
import Itasca.Runtime.Interp.Control.NormalizeClosure
import Itasca.Runtime.Interp.Control.NormalizeCompose
import Itasca.Runtime.Interp.Machines.Slice.SliceMeasure
import Itasca.Runtime.Store.Invariant.SemanticApi
import Itasca.Runtime.Store.Invariant.Syntax
import Itasca.Runtime.Spec.Mutation
import Itasca.Runtime.Interp.Memory.MemoryMutation
import Itasca.Runtime.Theorems.Composition.Core.CoreContents
import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Store.Invariant.FunctionTables
import Itasca.Runtime.Code.Local.Relations.Common.CoreFunctionContext
import Itasca.Runtime.Store.Invariant.CoreTypingExtension
import Itasca.Runtime.Store.Invariant.ObjectExtension
import Itasca.Runtime.Theorems.Composition.GlobalMutationShape
import Itasca.Runtime.Theorems.Composition.Core.CoreOwnership
import Itasca.Runtime.Store.Invariant.InstantiationCode
import Itasca.Runtime.Store.Initialization.SegmentObjectMetadata
import Itasca.Runtime.Theorems.Composition.Supported.SupportedSimdExecution
import Itasca.Runtime.Theorems.Composition.Supported.SupportedTypedSelectExecution
import Itasca.Runtime.Interp.StructuredMachine.EpilogueExecution
import Itasca.Runtime.Theorems.Composition.Supported.SupportedNormalizeOutcome
import Itasca.Runtime.Interp.StructuredMachine.NormalizeExecution
import Itasca.Runtime.Interp.StructuredMachine.PendingExecution
import Itasca.Runtime.Theorems.Composition.Supported.SupportedMeasure
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
