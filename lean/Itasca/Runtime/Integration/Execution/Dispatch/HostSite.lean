import Itasca.Runtime.Integration.Execution.Dispatch.BranchTable
import Itasca.Runtime.Integration.Execution.Dispatch.Outcomes
import Itasca.Runtime.Integration.Execution.Mutation.Operations
import Itasca.Runtime.Interp.Machine.Global.Mutation
import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryAdvance
import Itasca.Runtime.Interp.Machine.Select
import Itasca.Runtime.Interp.Machine.Global.ExecutionOwned
import Itasca.Runtime.Interp.Machine.Constants.FloatConstant
import Itasca.Runtime.Interp.Machine.Normalization
import Itasca.Runtime.Interp.Machine.Calls.HostCallStack
import Itasca.Runtime.Interp.Machine.Frames.FrameDepth
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
import Itasca.Runtime.Interp.Machine.Coverage.RecordingHeads
import Itasca.Runtime.Interp.Machine.Coverage.SyntaxClosure
import Itasca.Runtime.Integration.Execution.Dispatch.Scalar
import Itasca.Runtime.Integration.Execution.Dispatch.StoreOperations
import Itasca.Runtime.Integration.Execution.Dispatch.IndirectExecution
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.SourceMachine.Measure
import Itasca.Runtime.Interp.Relations.SuspendedPoint
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Interp.Machine.Frames.Reposition
import Itasca.Runtime.SourceMachine.Core.Trap
import Itasca.Runtime.SourceMachine.Ownership.Extension
import Itasca.Runtime.Interp.Machine.Mutation.Core
import Itasca.Runtime.Interp.Relations.SourceCallCause
import Itasca.Runtime.Interp.State.GlobalMutationStep
import Itasca.Runtime.Interp.Relations.ReferenceTransfers
import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Interp.Machine.Emission.Local
import Itasca.Runtime.Interp.Relations.PrefixDispatch
import Itasca.Runtime.SourceMachine.Core.SelectPositive
import Itasca.Runtime.Interp.Relations.ControlPoint
import Itasca.Runtime.Interp.Numeric.Integer.NumericFetch
import Itasca.Runtime.Interp.Numeric.Integer.NumericCodePoint
import Itasca.Runtime.SourceMachine.Numeric.TransitionSimulation
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredCodeTableExclusion
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryExecution
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryStack
import Itasca.Runtime.Interp.Machine.Frames.StackPreservation
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.Interp.Relations.PrefixEffect
import Itasca.Runtime.Interp.Control.BrTableSource
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.Bound
import Itasca.Runtime.Spec.Integer
import Itasca.Runtime.Interp.Machine.Retention.Ownership
import Itasca.Runtime.Interp.Relations.LocalCodePoint
import Itasca.Runtime.Interp.Relations.Fetch
import Itasca.Runtime.Interp.Relations.ValueLookup
import Itasca.Runtime.Interp.Relations.LocalCapacity
import Itasca.Runtime.Interp.Relations.Capacity
import Itasca.Runtime.Interp.Machine.Local.ExecutionOwned
import Itasca.Runtime.Interp.Machine.Retention.ReturnedOwnership
import Itasca.Runtime.Interp.Machine.Retention.CodeBounds
import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.Interp.Control.NormalizeCompose
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Interp.Relations.ControlEntry
import Itasca.Runtime.Interp.State.GlobalCoreStep
import Itasca.Runtime.Interp.State.GlobalCoreOperands
import Itasca.Runtime.Compiler.Local.Capacity.GlobalCapacity
import Itasca.Runtime.Interp.Relations.SelectSlots
import Itasca.Runtime.Interp.Machine.Select.Operands
import Itasca.Runtime.Interp.Memory.MemoryCoreTransition
import Itasca.Runtime.Interp.Memory.MemoryCoreOperandBounds
import Itasca.Runtime.Interp.Memory.MemoryCoreEmission
import Itasca.Runtime.Interp.Memory.MemoryCoreStep
import Itasca.Runtime.Interp.Memory.MemoryCoreResult
import Itasca.Runtime.Interp.Memory.MemoryLoadStepFootprint
import Itasca.Runtime.SourceMachine.BrTable
import Itasca.Runtime.SourceMachine.CallSafety
import Itasca.Runtime.Interp.Calls.IndirectResolve
import Itasca.Runtime.Compiler.Local.Relations.Function.CoreFunction
import Itasca.Runtime.Interp.Calls.ReturnRefinement
import Itasca.Runtime.Interp.Machine.Emission.Unreachable
import Itasca.Runtime.Interp.Relations.StackRelation
import Itasca.Runtime.Interp.Relations.Epilogue
import Itasca.Runtime.Interp.Relations.Normalization
import Itasca.Runtime.Interp.Control.LabelCompletion
import Itasca.Runtime.Interp.Machine.Simulation.CoreErasure
import Itasca.Runtime.Interp.Machine.Simulation.Measure
import Itasca.Runtime.Store.Invariant.SemanticApi
import Itasca.Runtime.Store.Invariant.Syntax
import Itasca.Runtime.Interp.Memory.MemoryMutation
import Itasca.Runtime.Integration.Execution.Ownership.Contents
import Itasca.Runtime.Representation.Values
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
import Itasca.Runtime.Integration.Execution.Dispatch.Normalization
import Itasca.Runtime.Interp.Machine.Normalization.NormalizeExecution
import Itasca.Runtime.Interp.Machine.Progress.PendingExecution
import Itasca.Runtime.Integration.Execution.Dispatch.Measure

namespace Itasca.Runtime.Integration
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
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) where
  index : Usize
  raw : runtime.interp.Frame
  inst : runtime.store.ModuleInst
  compiled : runtime.bytecode.CompiledFunction
  context : _root_.context
  targets : List Compiler.LabelTarget
  next : Nat
  output : List valtype
  last : index.val+1=exec.frames.length
  frameAt : exec.frames.val[index.val]?=some raw
  instanceAt : store.instances.val[raw.instance.val]?=some inst
  compiledAt : inst.module.functions.val[raw.function.val]?=some compiled
  program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes context.FUNCS
  slots : FrameSlots exec raw f
  moduleEq : f.module=Store.decodeInstance store inst
  point : Machine.FramePoint (Store.decodeStore view code store) raw f compiled context targets next output
  machine : Machine.Execution view code store exec
    ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ expected raw.pc.val false
  owned : SourceMachine.Ownership.StateOwned (Store.ownershipBounds store)
    ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩

/-- Actual common dispatch yields one of these sites or an ordinary checked
step. Source-only normalization is retained for the later eventful join. -/
inductive StructuredHostSite {M : Type}
    (view : M → Slice U8) (code : Store.CodeInterpretation) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (expected : List valtype) : Nat → Bool → SourceMachine.AState → Prop where
  | ready {ambient : frame} {f : SourceMachine.AFrame} {rest : List SourceMachine.AFrame} {op : instr} {after : List instr}
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
end Itasca.Runtime.Integration
