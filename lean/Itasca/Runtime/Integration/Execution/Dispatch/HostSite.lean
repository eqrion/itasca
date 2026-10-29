import Itasca.Runtime.Integration.Execution.Dispatch.BranchTable
import Itasca.Runtime.Integration.Execution.Dispatch.Outcomes
import Itasca.Runtime.Integration.Execution.Mutation.Operations
import Itasca.Runtime.Interp.Machine.Global.Mutation
import Itasca.Runtime.Interp.Machine.Coverage.SupportedHeadCoverage
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryAdvance
import Itasca.Runtime.Interp.Machine.Numeric
import Itasca.Runtime.Interp.Machine.Global.ExecutionOwned
import Itasca.Runtime.Interp.Machine.Constants.FloatConstant
import Itasca.Runtime.Interp.Machine.Select
import Itasca.Runtime.Interp.Machine.Memory
import Itasca.Runtime.Interp.Machine.Calls.CallExecution
import Itasca.Runtime.Interp.Machine.Frames.ReturnExecution
import Itasca.Runtime.Interp.Machine.Progress.UnreachableExecution
import Itasca.Runtime.SourceMachine.Cumulative.Step
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEmission
import Itasca.Runtime.Interp.Relations.CompiledFunctions
import Itasca.Runtime.Compiler.Local.Control.Function.CumulativeFunctionContext
import Itasca.Runtime.Interp.Machine.Functions.CompiledFunctions
import Itasca.Runtime.Compiler.Body.Control.Table.CumulativeTableExclusion
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredCodePoint
import Itasca.Runtime.Interp.Machine.Coverage.SupportedControlSemantics
import Itasca.Runtime.Interp.Machine.Coverage.SupportedBoundarySemantics
import Itasca.Runtime.Integration.Execution.Dispatch.Scalar
import Itasca.Runtime.Integration.Execution.Dispatch.StoreOperations
import Itasca.Runtime.Integration.Execution.Dispatch.IndirectExecution
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.SourceMachine.ModuleBindingsExtension
import Itasca.Runtime.Interp.Relations.SuspendedPoint
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Interp.Machine.Frames.Reposition
import Itasca.Runtime.SourceMachine.Core.Typing
import Itasca.Runtime.SourceMachine.Core
import Itasca.Runtime.SourceMachine.Ownership.Core
import Itasca.Runtime.Interp.Machine.Mutation.Core
import Itasca.Runtime.Interp.Relations.SourceCallCause
import Itasca.Runtime.Interp.State.GlobalMutationStep
import Itasca.Runtime.Interp.Control.PendingJump
import Itasca.Runtime.Interp.Relations.ReferenceTransfers
import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Interp.Machine.Emission.Integer
import Itasca.Runtime.Interp.Relations.PrefixDispatch
import Itasca.Runtime.SourceMachine.Core.Correct
import Itasca.Runtime.Interp.Relations.ControlPoint
import Itasca.Runtime.Interp.Numeric.Integer.NumericFetch
import Itasca.Runtime.Interp.Numeric.Integer.NumericCodePoint
import Itasca.Runtime.SourceMachine.Numeric.TransitionSimulation
import Itasca.Runtime.SourceMachine.Core.Bound
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredCodeTableExclusion
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryExecution
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryStack
import Itasca.Runtime.Interp.Machine.Frames.StackPreservation
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.Interp.Relations.PrefixEffect
import Itasca.Runtime.Interp.Control.SkipStack
import Itasca.Runtime.SourceMachine.Core.Step
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.StepSafety
import Itasca.Runtime.SourceMachine.Core.Pure
import Itasca.Runtime.Spec.Extend
import Itasca.Runtime.Interp.Machine.Retention.Ownership
import Itasca.Runtime.Interp.Machine.Emission.Local
import Itasca.Runtime.Interp.Relations.LocalCodePoint
import Itasca.Runtime.Interp.Relations.Fetch
import Itasca.Runtime.Interp.Relations.ValueLookup
import Itasca.Runtime.Interp.Relations.LocalCapacity
import Itasca.Runtime.Interp.Relations.Capacity
import Itasca.Runtime.Interp.Machine.Local.MovePrefix
import Itasca.Runtime.Interp.Machine.Retention.ReturnedOwnership
import Itasca.Runtime.Interp.Machine.Retention.CodeBounds
import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.Interp.Control.BranchNoCopy
import Itasca.Runtime.Interp.Control.BranchConditionStep
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Interp.Relations.ControlEntry
import Itasca.Runtime.Interp.Control.LoopHead
import Itasca.Runtime.Interp.Machine.Constants.IntegerEmission
import Itasca.Runtime.Interp.Machine.Constants.IntegerSlots
import Itasca.Runtime.Interp.Machine.Emission.Opcode
import Itasca.Runtime.Interp.State.GlobalCoreStep
import Itasca.Runtime.Interp.State.GlobalCoreOperands
import Itasca.Runtime.Compiler.Local.Capacity.GlobalCapacity
import Itasca.Runtime.Interp.Machine.Constants.FloatEmission
import Itasca.Runtime.Interp.Machine.Constants.FloatSlots
import Itasca.Runtime.Interp.Relations.SelectSlots
import Itasca.Runtime.Interp.Machine.Select.Operands
import Itasca.Runtime.Interp.Memory.MemoryCoreTransition
import Itasca.Runtime.Interp.Memory.MemoryCoreOperandBounds
import Itasca.Runtime.Interp.Memory.MemoryCoreEmission
import Itasca.Runtime.Interp.Memory.MemoryCoreStep
import Itasca.Runtime.Interp.Memory.MemoryCoreResult
import Itasca.Runtime.Interp.Memory.MemoryLoadStepFootprint
import Itasca.Runtime.SourceMachine.Bound
import Itasca.Runtime.SourceMachine.ReferenceBounds
import Itasca.Runtime.Interp.Machine.Functions.Typing
import Itasca.Runtime.SourceMachine.CallSafety
import Itasca.Runtime.Interp.Calls.CallStack
import Itasca.Runtime.Compiler.Local.Relations.Function.CoreFunction
import Itasca.Runtime.Interp.Calls.CallRefinement
import Itasca.Runtime.SourceMachine.Results
import Itasca.Runtime.Interp.Calls.ReturnRefinement
import Itasca.Runtime.Interp.Calls.ReturnResult
import Itasca.Runtime.Interp.Machine.Emission.Unreachable
import Itasca.Runtime.Interp.Relations.StackRelation
import Itasca.Runtime.Interp.Relations.Epilogue
import Itasca.Runtime.Interp.Relations.Normalization
import Itasca.Runtime.Interp.Machine.Emission.Empty
import Itasca.Runtime.Interp.Control.LabelCompletion
import Itasca.Runtime.Interp.Machine.Simulation.CoreErasure
import Itasca.Runtime.Interp.Control.NormalizeClosure
import Itasca.Runtime.Interp.Control.NormalizeCompose
import Itasca.Runtime.Interp.Machine.Simulation.Measure
import Itasca.Runtime.Store.Invariant.SemanticApi
import Itasca.Runtime.Store.Invariant.Syntax
import Itasca.Runtime.Spec.Mutation
import Itasca.Runtime.Interp.Memory.MemoryMutation
import Itasca.Runtime.Integration.Execution.Ownership.Contents
import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Store.Invariant.FunctionTables
import Itasca.Runtime.Compiler.Local.Relations.Function.CoreFunctionContext
import Itasca.Runtime.Store.Invariant.CoreTypingExtension
import Itasca.Runtime.Store.Invariant.ObjectExtension
import Itasca.Runtime.Integration.Execution.Mutation.GlobalShape
import Itasca.Runtime.Integration.Execution.Ownership.Entry
import Itasca.Runtime.Store.Invariant.InstantiationCode
import Itasca.Runtime.Store.Initialization.SegmentObjectMetadata
import Itasca.Runtime.Integration.Execution.Dispatch.Simd
import Itasca.Runtime.Integration.Execution.Dispatch.TypedSelect
import Itasca.Runtime.Interp.Machine.Frames.EpilogueExecution
import Itasca.Runtime.Integration.Execution.Dispatch.Normalization
import Itasca.Runtime.Interp.Machine.Normalization.NormalizeExecution
import Itasca.Runtime.Interp.Machine.Progress.PendingExecution
import Itasca.Runtime.Integration.Execution.Dispatch.Measure
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
