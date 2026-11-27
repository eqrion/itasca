import Itasca.Runtime.Integration.Execution.Dispatch.MemoryAndSelect
import Itasca.Runtime.Integration.Execution.Resources.InvocationErrors
import Itasca.Runtime.Integration.Execution.Mutation.Operations
import Itasca.Runtime.Interp.Machine.Progress.SupportedAdvance
import Itasca.Runtime.Interp.Machine.Progress.UnreachableExecution
import Itasca.Runtime.SourceMachine.Float.Transition
import Itasca.Runtime.Interp.Machine.Control.BranchSource
import Itasca.Runtime.Interp.Machine.Normalization.IndexedEmpty
import Itasca.Runtime.Interp.Machine.StateAndOwnership
import Itasca.Runtime.Interp.Machine.Simd.FrameStep
import Itasca.Runtime.Integration.Execution.Dispatch.Stateful
import Itasca.Runtime.Integration.Api.GrowthAndValueSupport
import Itasca.Runtime.Integration.Execution.Dispatch.Normalization
import Itasca.Runtime.Interp.Machine.ScalarExecution
import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Interp.Machine.Progress.PendingExecution
import Itasca.Runtime.Interp.Machine.Constants.EncodingAndFloat
import Itasca.Runtime.Interp.Machine.Calls.HostCallStack
import Itasca.Runtime.Interp.Machine.Frames.ReturnsAndDepth
import Itasca.Runtime.SourceMachine.TransitionAndHostPreparation
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowered
import Itasca.Runtime.Interp.Relations.ReadbackAndBindings
import Itasca.Runtime.Compiler.Local.Control.FunctionAssembly
import Itasca.Runtime.Interp.Machine.CompiledFunctions
import Itasca.Runtime.Compiler.Body.Control.StructuredPrefixes
import Itasca.Runtime.Compiler.Local.Control.CodeSegmentsAndPositions
import Itasca.Runtime.Compiler.Local.Control.Structured.Prefixes
import Itasca.Runtime.Interp.Machine.Coverage.RecordingHeads
import Itasca.Runtime.Interp.Machine.Coverage.SyntaxClosure
import Itasca.Runtime.Compiler.Local.Definitions
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.SourceMachine.StructureAndTyping
import Itasca.Runtime.Interp.Machine.Frames.Reposition
import Itasca.Runtime.SourceMachine.Core.OperationsAndMemoryTyping
import Itasca.Runtime.SourceMachine.OwnershipExtension
import Itasca.Runtime.Interp.Relations.SourceCallCause
import Itasca.Runtime.Interp.State.ObjectBindingsAndMutation
import Itasca.Runtime.Interp.Relations.NormalizationAndValueTypes
import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Interp.Machine.Emission.Local
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.SourceMachine.Core.ProgressAndBounds
import Itasca.Runtime.Interp.Numeric.Integer.ConversionsAndBinaryContracts
import Itasca.Runtime.Interp.Numeric.Integer.SignedOperationsAndCounts
import Itasca.Runtime.SourceMachine.Numeric.TransitionSimulation
import Itasca.Runtime.Interp.Machine.Frames.FrameAndReturnStacks
import Itasca.Runtime.Interp.Control.BrTableSource
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.Bound
import Itasca.Runtime.Spec.TypingAndNumericOperations
import Itasca.Runtime.Interp.Machine.Retention.ReturnedOwnership
import Itasca.Runtime.Interp.Relations.EntryEffects
import Itasca.Runtime.Interp.Relations.SlotsAndDefaults
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.Interp.Control.NormalizeCompose
import Itasca.Runtime.Interp.State.GlobalOperations
import Itasca.Runtime.Compiler.Local.Capacity.ControlAvailability
import Itasca.Runtime.Interp.Machine.Select.Operands
import Itasca.Runtime.Interp.Memory.EncodingAndDispatch
import Itasca.Runtime.Interp.Memory.MemoryEffects
import Itasca.Runtime.SourceMachine.EntryAndBranchTables
import Itasca.Runtime.SourceMachine.Preservation
import Itasca.Runtime.Interp.Calls.OutcomesAndResolution
import Itasca.Runtime.Compiler.Local.Relations.Function.CapturedContext
import Itasca.Runtime.Interp.Calls.ReturnRefinement
import Itasca.Runtime.Interp.Machine.Emission.Unreachable
import Itasca.Runtime.Interp.Control.LabelCompletion
import Itasca.Runtime.Store.Invariant.SemanticApi
import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.Integration.Execution.Ownership.Publication
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Integration.Execution.Mutation.BulkResult
import Itasca.Runtime.Store.Initialization.SegmentSourceStaging
import Itasca.Runtime.Interp.Machine.Normalization.NormalizeExecution
import Itasca.Runtime.Platform.Laws

/-!
Proofs for Runtime / Integration / Execution / Dispatch.

This module collects ScalarAndSimd, Host.
Each section documents its contracts and consumers.
-/

/-! ## ScalarAndSimd -/

section

open Itasca.Representation

/-!
# Scalar And Simd

Uniform scalar and SIMD dispatch outcomes preserve the execution interpretation at each instruction boundary.
-/

/-! ## UniformOutcomes -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std Itasca.Interp
/-- Concrete mutation evidence and the full source/machine outcome of one
cumulative dispatch. Fresh certification follows from the mutation witness. -/
def UniformSupportedStepOutcome {M P A : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (expected : List valtype) (codeLength pc : Nat) (pending : Bool) (source : SourceMachine.AState)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : Prop :=
  CumulativeStoreMutation view code store out.2.2.1 ∧
    match out.1 with
    | .Ok _ => Machine.UniformAdvance view code out.2.2.1 out.2.1 expected codeLength pc pending source
    | .Err error => CumulativeFailure allocator hooks exec store platform source error ∧
      Representation.decodeStore view code out.2.2.1=source.store

variable {M P A : Type} {allocator : runtime.platform.Alloc A} {hooks : runtime.platform.Platform P M}
  {view : M → Slice U8} {code : Representation.CodeInterpretation} {exec : runtime.interp.Execution}
  {store : runtime.store.Store M} {platform : P} {expected : List valtype}
  {codeLength pc : Nat} {pending : Bool} {source : SourceMachine.AState}
  {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}

theorem UniformSupportedStepOutcome.success (mutation : CumulativeStoreMutation view code store out.2.2.1)
    (status : out.1=.Ok ())
    (advance : Machine.UniformAdvance view code out.2.2.1 out.2.1 expected codeLength pc pending source) :
    UniformSupportedStepOutcome allocator hooks view code exec store platform expected codeLength pc pending source out :=
  ⟨mutation,by simpa only [status] using advance⟩

theorem UniformSupportedStepOutcome.unchanged_success (shaped : Representation.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store)
    (same : out.2.2.1=store) (status : out.1=.Ok ())
    (advance : Machine.UniformAdvance view code store out.2.1 expected codeLength pc pending source) :
    UniformSupportedStepOutcome allocator hooks view code exec store platform expected codeLength pc pending source out := by
  apply UniformSupportedStepOutcome.success (by rw [same]; exact .refl_of_shape shaped sourceSyntax bounds) status
  simpa only [same] using advance

theorem UniformSupportedStepOutcome.failure (mutation : CumulativeStoreMutation view code store out.2.2.1)
    {error : runtime.ExecError} (status : out.1=.Err error)
    (decoded : Representation.decodeStore view code out.2.2.1=source.store)
    (cause : CumulativeFailure allocator hooks exec store platform source error) :
    UniformSupportedStepOutcome allocator hooks view code exec store platform expected codeLength pc pending source out :=
  ⟨mutation,by simpa only [status] using And.intro cause decoded⟩

theorem UniformSupportedStepOutcome.forget
    (outcome : UniformSupportedStepOutcome allocator hooks view code exec store platform expected codeLength pc pending source out) :
    SupportedStepOutcome allocator hooks view code exec store platform expected codeLength pc pending source out := by
  obtain ⟨mutation, outcome⟩ := outcome
  refine ⟨mutation, ?_⟩
  cases status : out.1 with
  | Ok value => exact (by simpa only [status] using outcome : Machine.UniformAdvance view code out.2.2.1 out.2.1 expected codeLength pc pending source).forget
  | Err error => simpa only [status] using outcome
end Itasca.Integration

end

/-! ## Scalar -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly SourceMachine.Float Itasca.Interp

/-- All seventy scalar float operators preserve the mutable float machine or
return the exact generated arithmetic trap; allowed NaN choices remain relational. -/
theorem step_scalar_supported_execution_uniform
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (op : Instruction) (after : List instr)
    (last : index.val+1 = exec.frames.length) (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : Machine.FramePoint (Representation.decodeStore view code store) raw {f with code := op.source::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Machine.Execution view code store exec
      ⟨Representation.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS)
    (shaped : Representation.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store) :
    let initial : SourceMachine.AState := ⟨Representation.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      UniformSupportedStepOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false initial out ⦄ := by
  dsimp only
  have pcBound : raw.pc.val < U32.max := by
    have linear : linearSource op.source = true := by cases op <;> rfl
    rcases Machine.structured_code_linear_inv linear point.code.current with skip | branch
    · obtain ⟨target,forward,fetched,continuation⟩ := skip
      have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have cap := program.fetchBound
      omega
    · obtain ⟨middle,emitted,tail,head,fragment,continuation⟩ := branch
      obtain ⟨stack,left,right,shape,middleEq,emittedEq,leftPos,rightPos⟩ := (Machine.FloatHeads.project (.float op) head).float_inv op
      have fetched : compiled.code.val[raw.pc.val]? = some (Compiler.floatInstruction op left left right) := by
        simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq,List.getElem?_cons_zero])
      have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have cap := program.fetchBound
      omega
  apply WP.spec_mono (Machine.step_float_structured_owned memory hooks floats allocator correct exec store platform index raw inst compiled
    C targets next output (Representation.decodeStore view code store) ambient f rest op after last frameFound instanceFound codeFound
    pcBound machine.typed.typed slots point)
  intro out effect
  obtain ⟨sameStore,samePlatform,operation⟩ := effect
  refine ⟨sameStore,samePlatform,?_⟩
  rcases operation with ⟨success,pc,g,fields,represented,retained,typed,metadata,simulation,prefixEffect,owned,transition⟩ |
    ⟨trap,failed,kind,count,positive,source⟩
  · have uniform : UniformConcreteSim raw.pc.val pc.val false false
        ⟨Representation.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩
        ⟨Representation.decodeStore view code store,ambient,g::rest,[]⟩ [] := by
      rcases transition with same | actual
      · subst g
        exact simulation.uniform_same (by scalar_tac)
      · exact UniformConcreteSim.single (SourceMachine.Float.transition_positive _ _ _ _ _ _ _ machine.typed.typed actual)
    have facts : SourceMachine.CoreTyped ⟨Representation.decodeStore view code store,ambient,g::rest,[]⟩ ∧
        SourceMachine.SupportedState ⟨Representation.decodeStore view code store,ambient,g::rest,[]⟩ ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds ⟨Representation.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩ →
          SourceMachine.Ownership.StatefulOwned bounds ⟨Representation.decodeStore view code store,ambient,g::rest,[]⟩) ∧
        (∀ bound, SourceMachine.CodeBound bound ⟨Representation.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩ →
          SourceMachine.CodeBound bound ⟨Representation.decodeStore view code store,ambient,g::rest,[]⟩) := by
      rcases transition with same | actual
      · subst g
        exact ⟨machine.typed,machine.core,fun _ owned => owned,fun _ bounded => bounded⟩
      · have step : SourceMachine.Cumulative.Step ⟨Representation.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩
            (.next ⟨Representation.decodeStore view code store,ambient,g::rest,[]⟩) := .scalar actual
        exact ⟨step.next_typed_supported machine.typed machine.core,step.next_covered_supported machine.typed machine.core,
          fun _ invariant => step.next_owned_supported machine.typed machine.core invariant,
          fun _ invariant => step.next_bound_supported machine.typed machine.core invariant⟩
    have fresh := Machine.Execution.ordinary view code ambient {f with code := op.source::after} g rest expected raw.pc.val false machine
      (.refl store) (Itasca.Spec.extend_store_refl _ machine.typed.typed.store) raw index pc last frameFound program
      (.ready retained) represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ fields prefixEffect facts.1 facts.2.1
    exact UniformSupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore success
      ⟨pc.val,false,_,fresh,simulation,uniform,facts.2.2.1,rfl,facts.2.2.2⟩
  · apply UniformSupportedStepOutcome.failure (by rw [sameStore]; exact .refl_of_shape shaped sourceSyntax bounds) failed (by rw [sameStore])
    apply Or.inl
    refine ⟨⟨trap,rfl,Or.inl ?_⟩,count,positive,source⟩
    rcases kind with overflow | conversion
    · exact Or.inr (Or.inr (Or.inl overflow))
    · exact Or.inr (Or.inr (Or.inr (Or.inr conversion)))
theorem step_scalar_supported_execution
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (op : Instruction) (after : List instr)
    (last : index.val+1 = exec.frames.length) (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : Machine.FramePoint (Representation.decodeStore view code store) raw {f with code := op.source::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Machine.Execution view code store exec
      ⟨Representation.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS)
    (shaped : Representation.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store) :
    let initial : SourceMachine.AState := ⟨Representation.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      SupportedStepOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false initial out ⦄ := by
  apply WP.spec_mono (step_scalar_supported_execution_uniform memory hooks floats allocator correct exec store platform index raw inst compiled C targets next output view code ambient f rest op after last frameFound instanceFound codeFound slots point expected machine program shaped sourceSyntax bounds)
  rintro out ⟨same,platform,outcome⟩
  exact ⟨same,platform,outcome.forget⟩

end Itasca.Integration

end

/-! ## Simd -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std Itasca.Interp
theorem step_simd_supported_execution {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (interpretation : Representation.CodeInterpretation)
    (memoryLaws : Platform.MemoryLaws memory view) (floatLaws : Platform.FloatOpsCorrect floats)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (raw : runtime.interp.Frame) (index : Usize) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction)
    [Machine.SimdProjection (emission compiled) compiled.simd.val compiled.v128_pool.val] (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (source : instr) (after : List instr) (expected : List valtype)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst)
    (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : Machine.FramePoint (Representation.decodeStore view interpretation store) raw
      {f with code:=source::after} compiled C targets next output)
    (simd : SourceMachine.SimdInstr source)
    (machine : Machine.Execution view interpretation store exec
      ⟨Representation.decodeStore view interpretation store,ambient,{f with code:=source::after}::rest,[]⟩ expected raw.pc.val false)
    (shaped : Representation.Shape view store) (sourceSyntax : Store.StoreSyntax interpretation store)
    (bounds : Store.SegmentBounds store) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SupportedStepOutcome allocator hooks view interpretation exec store platform expected compiled.code.length raw.pc.val false
        ⟨Representation.decodeStore view interpretation store,ambient,{f with code:=source::after}::rest,[]⟩ out ⦄ := by
  apply WP.spec_mono (Machine.Simd.step_execution memory hooks floats allocator view interpretation memoryLaws floatLaws
    exec store platform raw index inst compiled C targets next output ambient f rest source after expected last hf hi hc program slots point simd
    (fun _ _ _ head => Machine.SimdProjection.project simd head) machine)
  intro out effect
  obtain ⟨platformEq,rawMutation,metadata,extension,normal | failed⟩ := effect
  · have mutation : CumulativeStoreMutation view interpretation store out.2.2.1 := by
      rcases rawMutation with same | ⟨address,object,issued,changed⟩
      · rw [same]; exact .refl_of_shape shaped sourceSyntax bounds
      · exact memory_mutation_cumulative_of_shape view interpretation store _ shaped sourceSyntax bounds address object issued changed
    obtain ⟨success,pc,g,fresh,simulation,owned,bounded⟩ := normal
    exact SupportedStepOutcome.success mutation success
      (Machine.Advance.of_frame fresh simulation owned rfl bounded)
  · have mutation : CumulativeStoreMutation view interpretation store out.2.2.1 := by
      rcases rawMutation with same | ⟨address,object,issued,changed⟩
      · rw [same]; exact .refl_of_shape shaped sourceSyntax bounds
      · exact memory_mutation_cumulative_of_shape view interpretation store _ shaped sourceSyntax bounds address object issued changed
    obtain ⟨error,decoded,trace⟩ := failed
    apply SupportedStepOutcome.failure mutation error decoded
    rw [decoded] at trace
    exact Or.inl ⟨⟨.MemoryOutOfBounds,rfl,Or.inl (by simp [FloatCoreTrap])⟩,trace⟩
end Itasca.Integration

end

end

/-! ## Host -/

section

open Itasca.Representation

/-!
# Host

Store-operation dispatch identifies actual host-call sites and outcomes. The joined host case retains concrete effects and the source execution interpretation.
-/

/-! ## StoreOperations -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std Itasca.Interp
theorem stateful_execution_supported
 {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [Machine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (op : SourceMachine.Stateful.Instruction)
    (last : index.val+1=exec.frames.length)
    (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module=Representation.decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : Machine.FramePoint (Representation.decodeStore view code store) raw {f with code:=op.source::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Machine.Execution view code store exec
      ⟨Representation.decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS)
    (shaped : Representation.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store)
    (owned : SourceMachine.Ownership.StatefulOwned (Store.ownershipBounds store) ⟨Representation.decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SupportedStepOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Representation.decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩ out ⦄ := by
  cases op with
  | refNull type =>
    exact stateful_read_execution_supported memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output ambient f rest after (.refNull type) rfl last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | refFunc function =>
    exact stateful_read_execution_supported memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output ambient f rest after (.refFunc function) rfl last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | refIsNull  =>
    exact stateful_read_execution_supported memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output ambient f rest after (.refIsNull) rfl last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | tableGet table =>
    exact stateful_read_execution_supported memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output ambient f rest after (.tableGet table) rfl last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | tableSize table =>
    exact stateful_read_execution_supported memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output ambient f rest after (.tableSize table) rfl last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | memorySize  =>
    exact stateful_read_execution_supported memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output ambient f rest after (.memorySize) rfl last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | tableSet table =>
    exact stateful_table_set_execution_supported memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output ambient f rest after table last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds owned
  | tableGrow table =>
    exact stateful_table_grow_execution_supported memory hooks floats allocator allocation view code exec store platform index raw inst compiled C targets next output ambient f rest after table last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds owned
  | tableFill table =>
    exact stateful_table_fill_execution_supported memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output ambient f rest after table last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds owned
  | tableCopy destination source =>
    exact stateful_table_copy_execution_supported memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output ambient f rest after destination source last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | tableInit table element =>
    exact stateful_table_init_execution_supported memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output ambient f rest after table element last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | memoryGrow  =>
    exact stateful_memory_grow_execution_supported memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output ambient f rest after  last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | memoryFill  =>
    exact stateful_memory_fill_execution_supported memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output ambient f rest after  last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | memoryCopy  =>
    exact stateful_memory_copy_execution_supported memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output ambient f rest after  last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | memoryInit data =>
    exact stateful_memory_init_execution_supported memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output ambient f rest after data last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | elemDrop element =>
    exact stateful_drop_execution_supported memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output ambient f rest after (.elemDrop element) rfl last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | dataDrop data =>
    exact stateful_drop_execution_supported memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output ambient f rest after (.dataDrop data) rfl last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds

end Itasca.Integration

end

/-! ## HostSite -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std Itasca.Interp

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
    (view : M → Slice U8) (code : Representation.CodeInterpretation) (exec : runtime.interp.Execution)
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
  program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes context.FUNCS
  slots : FrameSlots exec raw f
  moduleEq : f.module=Representation.decodeInstance store inst
  point : Machine.FramePoint (Representation.decodeStore view code store) raw f compiled context targets next output
  machine : Machine.Execution view code store exec
    ⟨Representation.decodeStore view code store,ambient,f::rest,[]⟩ expected raw.pc.val false
  owned : SourceMachine.Ownership.StateOwned (Store.ownershipBounds store)
    ⟨Representation.decodeStore view code store,ambient,f::rest,[]⟩

/-- Actual common dispatch yields one of these sites or an ordinary checked
step. Source-only normalization is retained for the later eventful join. -/
inductive StructuredHostSite {M : Type}
    (view : M → Slice U8) (code : Representation.CodeInterpretation) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (expected : List valtype) : Nat → Bool → SourceMachine.AState → Prop where
  | ready {ambient : frame} {f : SourceMachine.AFrame} {rest : List SourceMachine.AFrame} {op : instr} {after : List instr}
      (site : HostFrameSite view code exec store expected ambient {f with code:=op::after} rest)
      (kind : DirectHostInstruction store site.raw site.inst site.compiled op ∨
        ∃ table type : U32, op=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val) ∧
          SourceIndirectHostBoundary store ⟨Representation.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩) :
      StructuredHostSite view code exec store expected site.raw.pc.val false
        ⟨Representation.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩
  | normalize {count pc s ambient before after rest}
      (chain : ErasedSteps count before after)
      (site : StructuredHostSite view code exec store expected pc false ⟨s,ambient,after::rest,[]⟩) :
      StructuredHostSite view code exec store expected pc false ⟨s,ambient,before::rest,[]⟩
end Itasca.Integration

end

/-! ## Host -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Interp
theorem step_head_supported_host_site
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (op : instr) (after : List instr)
    (head : DispatchHead op)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (moduleEq : f.module = Representation.decodeInstance store inst)
    (small : ∀ object ∈ store.globals.val, object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32)
    (point : Machine.FramePoint (Representation.decodeStore view code store) raw {f with code := op::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Machine.Execution view code store exec ⟨Representation.decodeStore view code store,ambient,{f with code := op::after}::rest,[]⟩ expected raw.pc.val false)
    (shaped : Representation.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store)
    (compiledFunctions : Machine.CompiledFunctions code store) (functionTyping : CoreFunctionsTyped view code store)
    (owned : SourceMachine.Ownership.StatefulOwned (Store.ownershipBounds store)
      ⟨Representation.decodeStore view code store,ambient,{f with code := op::after}::rest,[]⟩) :
    StructuredHostSite view code exec store expected raw.pc.val false ⟨Representation.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩ ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SupportedStepOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Representation.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩ out ⦄ := by
  cases head with
  | ordinary operation =>
    apply Or.inr
    apply WP.spec_mono (Machine.step_ordinary_advance memory hooks floats allocator view code exec store platform index raw inst compiled
      C targets next output ambient f rest operation after last hf hi hc program slots point expected machine)
    intro out effect
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds effect.2.1 effect.1 effect.2.2.2
  | numeric operation =>
    apply Or.inr
    apply WP.spec_mono (Machine.step_numeric_execution_owned memory hooks floats allocator view code exec store platform index raw inst compiled
      C targets next output ambient f rest operation after last hf hi hc program slots point expected machine)
    intro out effect
    obtain ⟨sameStore,samePlatform,success | trapped⟩ := effect
    · obtain ⟨status,pc,g,machine,simulation,ownership,bounded⟩ := success
      exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (Machine.Advance.of_frame machine simulation ownership rfl bounded)
    · obtain ⟨trap,status,kind,count,positive,steps⟩ := trapped
      apply SupportedStepOutcome.failure (by rw [sameStore]; exact .refl_of_shape shaped sourceSyntax bounds) status (by simp only [sameStore])
      exact Or.inl ⟨⟨trap,rfl,Or.inl (by rcases kind with rfl | rfl <;> simp [FloatCoreTrap])⟩,count,positive,steps⟩
  | loop bt body =>
    apply Or.inr
    apply WP.spec_mono (Machine.step_loop_execution memory hooks floats allocator laws.interruptsReturn platform index view code exec store raw inst compiled
      ambient f rest bt body after C targets next output hi slots last hf hc program point expected machine)
    intro out effect
    obtain ⟨sameStore,success | stopped⟩ := effect
    · obtain ⟨status,pc,g,pending,machine,simulation,ownership,bounded⟩ := success
      exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (Machine.Advance.of_frame machine simulation ownership rfl bounded)
    · apply SupportedStepOutcome.failure (by rw [sameStore]; exact .refl_of_shape shaped sourceSyntax bounds) stopped.1 (by simp only [sameStore])
      exact Or.inr (Or.inl ⟨rfl,_,stopped.2⟩)
  | call functionIndex =>
    rcases Machine.step_call_execution memory hooks floats allocator laws.allocCorrect laws.interruptsReturn view code exec store platform index raw inst compiled
      C targets next output ambient f rest functionIndex after compiledFunctions functionTyping last hf hi hc slots program point expected machine with host | operation
    · obtain ⟨address,function,host,offset,fetched,mapped,issued,hostCode⟩ := host
      exact Or.inl (.ready ⟨index,raw,inst,compiled,C,targets,next,output,last,hf,hi,hc,program,slots,moduleEq,point,machine,owned.values⟩ (Or.inl ⟨functionIndex,offset,address,function,host,rfl,fetched,mapped,issued,hostCode⟩))
    · apply Or.inr
      apply WP.spec_mono operation
      intro out effect
      obtain ⟨sameStore,success,rejected⟩ := effect
      cases status : out.1 with
      | Ok unit =>
        cases unit
        obtain ⟨pc,source,machine,simulation,ownership,ambientEq,bounded⟩ := success status
        exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status ⟨pc,false,source,machine,simulation,ownership,ambientEq,bounded⟩
      | Err error =>
        apply SupportedStepOutcome.failure (by rw [sameStore]; exact .refl_of_shape shaped sourceSyntax bounds) status (by simp only [sameStore])
        exact Or.inr (Or.inr ⟨index,raw,inst,compiled,last,hf,hi,hc,Or.inl (rejected error status)⟩)
  | return_ =>
    apply Or.inr
    apply WP.spec_mono (Machine.step_return_execution memory hooks floats allocator view code exec store platform index raw inst compiled
      C targets next output ambient f rest after last hf hi hc program slots point expected machine)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,source,machine,simulation,ownership,ambientEq,bounded⟩ := effect
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status ⟨pc,false,source,machine,simulation,ownership,ambientEq,bounded⟩
  | unreachable =>
    apply Or.inr
    apply WP.spec_mono (Machine.Unreachable.step_unreachable_core_execution_owned memory hooks floats allocator exec store platform index raw inst compiled
      C targets next output view code ambient f rest after last hf hi hc slots point expected machine program)
    intro out effect
    obtain ⟨sameStore,samePlatform,pc,frames,success | trapped⟩ := effect
    · obtain ⟨status,machine,simulation,ownership⟩ := success
      exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (Machine.Advance.of_frame machine simulation ownership rfl (fun _ h => h))
    · apply SupportedStepOutcome.failure (by rw [sameStore]; exact .refl_of_shape shaped sourceSyntax bounds) trapped.1 (by simp only [sameStore])
      exact Or.inl ⟨⟨.Unreachable,rfl,Or.inl (by simp [FloatCoreTrap])⟩,trapped.2⟩
  | float32 bits =>
    apply Or.inr
    apply WP.spec_mono (Machine.FloatConstant.step_float32_execution_owned memory hooks floats allocator exec store platform index raw inst compiled
      C targets next output view code ambient f rest (Builtins.floatOfBits 32 bits.val) after last hf hi hc slots point expected machine program)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,g,machine,simulation,ownership,bounded⟩ := effect
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (Machine.Advance.of_frame machine simulation ownership rfl bounded)
  | float64 bits =>
    apply Or.inr
    apply WP.spec_mono (Machine.FloatConstant.step_float64_execution_owned memory hooks floats allocator exec store platform index raw inst compiled
      C targets next output view code ambient f rest (Builtins.floatOfBits 64 bits.val) after last hf hi hc slots point expected machine program)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,g,machine,simulation,ownership,bounded⟩ := effect
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (Machine.Advance.of_frame machine simulation ownership rfl bounded)
  | select =>
    apply Or.inr
    apply WP.spec_mono (Machine.Select.step_select_core_execution_owned memory hooks floats allocator exec store platform index raw inst compiled
      C targets next output view code ambient f rest after last hf hi hc slots point expected machine program)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,g,machine,simulation,ownership,bounded⟩ := effect
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (Machine.Advance.of_frame machine simulation ownership rfl bounded)
  | globalGet globalIndex =>
    apply Or.inr
    apply WP.spec_mono (Machine.Global.step_global_get_core_execution_owned memory hooks floats allocator platform index view code exec store raw inst compiled
      ambient f rest after globalIndex.val C targets next output hi moduleEq slots last hf hc program small point expected machine)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,g,machine,simulation,ownership,bounded⟩ := effect
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status (Machine.Advance.of_frame machine simulation ownership rfl bounded)
  | globalSet globalIndex =>
    apply Or.inr
    have pcBound : raw.pc.val < U32.max := by
      rcases Machine.Global.core_point_global_set_head globalIndex.val after point.code with ⟨target,forward,fetch,tail⟩ | operation
      · exact program.fetched_bound _ fetch
      · obtain ⟨ty,idx,src,front,indexEq,lookup,values,position,fetch,tail⟩ := operation
        exact program.fetched_bound _ fetch
    have mutation := Machine.Global.core_frame_point_global_set_store_mutation memory hooks floats allocator platform index view code exec store raw inst compiled
      ambient f rest after globalIndex.val C targets next output hi moduleEq slots last hf hc pcBound point machine.typed
    obtain ⟨out,run,effect⟩ := WP.spec_imp_exists (Machine.Global.step_global_set_core_execution_owned memory hooks floats allocator platform index view code exec store raw inst compiled
      ambient f rest after globalIndex.val C targets next output hi moduleEq slots last hf hc program point expected machine)
    rw [run,WP.spec_ok] at mutation ⊢
    obtain ⟨status,samePlatform,metadata,extension,pc,g,machine,simulation,ownership,bounded⟩ := effect
    exact SupportedStepOutcome.success (core_mutation_cumulative_of_shape view code store _ _ shaped sourceSyntax bounds owned.core mutation) status (Machine.Advance.of_frame machine simulation ownership rfl bounded)
  | load operation argument =>
    apply Or.inr
    apply WP.spec_mono (Machine.Memory.step_memory_load_execution_owned memory hooks floats allocator platform index view laws.memoryLaws code exec store raw inst compiled
      ambient f rest after operation argument C targets next output hi moduleEq slots last hf hc point expected machine program)
    intro out effect
    obtain ⟨samePlatform,changed,metadata,extension,success | trapped⟩ := effect
    · have mutation : CoreStoreMutation view ⟨Representation.decodeStore view code store,ambient,{f with code := operation.source argument::after}::rest,[]⟩ store out.2.2.1 := by
        rcases changed with same | ⟨address,object,issued,mutation⟩
        · rw [same]; exact .unchanged
        · exact .memory issued mutation
      obtain ⟨status,pc,g,machine,simulation,ownership,bounded⟩ := success
      exact SupportedStepOutcome.success (core_mutation_cumulative_of_shape view code store _ _ shaped sourceSyntax bounds owned.core mutation) status (Machine.Advance.of_frame machine simulation ownership rfl bounded)
    · have mutation : CoreStoreMutation view ⟨Representation.decodeStore view code store,ambient,{f with code := operation.source argument::after}::rest,[]⟩ store out.2.2.1 := by
        rcases changed with same | ⟨address,object,issued,mutation⟩
        · rw [same]; exact .unchanged
        · exact .memory issued mutation
      apply SupportedStepOutcome.failure (core_mutation_cumulative_of_shape view code store _ _ shaped sourceSyntax bounds owned.core mutation) trapped.1 trapped.2.1
      exact Or.inl ⟨⟨.MemoryOutOfBounds,rfl,Or.inl (by simp [FloatCoreTrap])⟩,trapped.2.2⟩
  | store operation argument =>
    apply Or.inr
    apply WP.spec_mono (Machine.Memory.step_memory_store_execution_owned memory hooks floats allocator platform index view laws.memoryLaws code exec store raw inst compiled
      ambient f rest after operation argument C targets next output hi moduleEq slots last hf hc point expected machine program)
    intro out effect
    obtain ⟨samePlatform,changed,metadata,extension,success | trapped⟩ := effect
    · have mutation : CoreStoreMutation view ⟨Representation.decodeStore view code store,ambient,{f with code := operation.source argument::after}::rest,[]⟩ store out.2.2.1 := by
        rcases changed with same | ⟨address,object,issued,mutation⟩
        · rw [same]; exact .unchanged
        · exact .memory issued mutation
      obtain ⟨status,pc,g,machine,simulation,ownership,bounded⟩ := success
      exact SupportedStepOutcome.success (core_mutation_cumulative_of_shape view code store _ _ shaped sourceSyntax bounds owned.core mutation) status (Machine.Advance.of_frame machine simulation ownership rfl bounded)
    · have mutation : CoreStoreMutation view ⟨Representation.decodeStore view code store,ambient,{f with code := operation.source argument::after}::rest,[]⟩ store out.2.2.1 := by
        rcases changed with same | ⟨address,object,issued,mutation⟩
        · rw [same]; exact .unchanged
        · exact .memory issued mutation
      apply SupportedStepOutcome.failure (core_mutation_cumulative_of_shape view code store _ _ shaped sourceSyntax bounds owned.core mutation) trapped.1 trapped.2.1
      exact Or.inl ⟨⟨.MemoryOutOfBounds,rfl,Or.inl (by simp [FloatCoreTrap])⟩,trapped.2.2⟩
  | float operation =>
    apply Or.inr
    apply WP.spec_mono (step_scalar_supported_execution memory hooks floats allocator laws.floatsCorrect exec store platform index raw inst compiled C targets next output
      view code ambient f rest operation after last hf hi hc slots point expected machine program shaped sourceSyntax bounds)
    intro out result
    exact result.2.2
  | stateful operation =>
    apply Or.inr
    exact stateful_execution_supported memory hooks floats allocator laws.allocCorrect view laws.memoryLaws code exec store platform index raw inst compiled C targets next output
      ambient f rest after operation last hf hi hc moduleEq slots point expected machine program shaped sourceSyntax bounds owned
  | indirect table type =>
    rcases step_indirect_supported_execution memory hooks floats allocator laws.allocCorrect laws.interruptsReturn view code exec store platform index raw inst compiled C targets next output
      ambient f rest table type after last hf hi hc moduleEq program slots point expected machine shaped compiledFunctions functionTyping with host | operation
    · exact Or.inl (.ready ⟨index,raw,inst,compiled,C,targets,next,output,last,hf,hi,hc,program,slots,moduleEq,point,machine,owned.values⟩ (Or.inr ⟨table,type,rfl,host⟩))
    · apply Or.inr
      apply WP.spec_mono operation
      intro out result
      cases status : out.1 with
      | Ok unit =>
        cases unit
        exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds result.1 status (result.2.1 status)
      | Err error =>
        apply SupportedStepOutcome.failure (by rw [result.1];exact .refl_of_shape shaped sourceSyntax bounds) status (by simp only [result.1])
        rcases result.2.2 error status with ⟨⟨trap,errorEq,kind⟩,steps⟩ | cause
        · exact Or.inl ⟨⟨trap,errorEq,Or.inr kind⟩,steps⟩
        · exact Or.inr (Or.inr ⟨index,raw,inst,compiled,last,hf,hi,hc,Or.inr ⟨code,cause⟩⟩)
  | simd operation =>
    apply Or.inr
    exact step_simd_supported_execution memory hooks floats allocator view code laws.memoryLaws laws.floatsCorrect exec store platform raw index inst compiled
      C targets next output ambient f rest op after expected last hf hi hc program slots point operation machine shaped sourceSyntax bounds
  | typedSelect declared =>
    apply Or.inr
    exact step_typed_select_supported_execution memory hooks floats allocator exec store platform index raw inst compiled C targets next output
      view code ambient f rest declared after last hf hi hc slots point expected machine program shaped sourceSyntax bounds
  | branchTable depths fallback =>
    apply Or.inr
    exact step_branch_table_supported memory hooks floats allocator view code exec store platform
      index raw inst compiled C targets next output ambient f rest after depths fallback expected last hf hi hc
      program slots point machine shaped sourceSyntax bounds

theorem step_ready_supported_host_site
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (moduleEq : f.module = Representation.decodeInstance store inst)
    (small : ∀ object ∈ store.globals.val, object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32)
    (point : Machine.FramePoint (Representation.decodeStore view code store) raw f compiled C targets next output)
    (expected : List valtype)
    (machine : Machine.Execution view code store exec ⟨Representation.decodeStore view code store,ambient,f::rest,[]⟩ expected raw.pc.val false)
    (ready : ReadySource f)
    (shaped : Representation.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store)
    (compiledFunctions : Machine.CompiledFunctions code store) (functionTyping : CoreFunctionsTyped view code store)
    (owned : SourceMachine.Ownership.StatefulOwned (Store.ownershipBounds store) ⟨Representation.decodeStore view code store,ambient,f::rest,[]⟩) :
    StructuredHostSite view code exec store expected raw.pc.val false ⟨Representation.decodeStore view code store,ambient,f::rest,[]⟩ ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SupportedStepOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Representation.decodeStore view code store,ambient,f::rest,[]⟩ out ⦄ := by
  cases source : f.code with
  | nil =>
    apply Or.inr
    have labels : f.labels=[] := by simpa only [ReadySource,source] using ready
    have same : {f with code:=[],labels:=[]}=f := by rw [←source,←labels]
    apply WP.spec_mono (Machine.step_function_end_execution memory hooks floats allocator view code exec store platform index raw inst compiled
      C targets next output ambient f rest last hf hi hc program slots (by simpa only [same] using point) expected (by simpa only [same] using machine))
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,nextSource,fresh,simulation,ownership,ambientEq,bounded⟩ := effect
    apply SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status
    exact ⟨pc,false,nextSource,fresh,by simpa only [same] using simulation,by simpa only [same] using ownership,ambientEq,by simpa only [same] using bounded⟩
  | cons op after =>
    have same : {f with code:=op::after}=f := by rw [←source]
    have head := Machine.frame_head_coverage point ready op after source
    have result := step_head_supported_host_site memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output
      ambient f rest op after head last hf hi hc program slots moduleEq small (by simpa only [same] using point) expected
      (by simpa only [same] using machine) shaped sourceSyntax bounds compiledFunctions functionTyping (by simpa only [same] using owned)
    simpa only [same] using result

theorem step_frame_supported_host_site
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (moduleEq : f.module = Representation.decodeInstance store inst)
    (small : ∀ object ∈ store.globals.val, object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32)
    (pending : Bool)
    (point : Machine.ControlPoint (Representation.decodeStore view code store) raw f compiled C targets next output pending)
    (expected : List valtype)
    (machine : Machine.Execution view code store exec ⟨Representation.decodeStore view code store,ambient,f::rest,[]⟩ expected raw.pc.val pending)
    (shaped : Representation.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store)
    (compiledFunctions : Machine.CompiledFunctions code store) (functionTyping : CoreFunctionsTyped view code store)
    (owned : SourceMachine.Ownership.StatefulOwned (Store.ownershipBounds store) ⟨Representation.decodeStore view code store,ambient,f::rest,[]⟩) :
    StructuredHostSite view code exec store expected raw.pc.val pending ⟨Representation.decodeStore view code store,ambient,f::rest,[]⟩ ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SupportedStepOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val pending
        ⟨Representation.decodeStore view code store,ambient,f::rest,[]⟩ out ⦄ := by
  cases point with
  | jump target fetched continuation =>
    apply Or.inr
    apply WP.spec_mono (Machine.step_pending_execution memory hooks floats allocator platform index view code exec store raw inst compiled
      ambient f rest C targets next output hi slots last hf hc program (.jump target fetched continuation) expected machine)
    intro out effect
    obtain ⟨status,sameStore,samePlatform,pc,retained,simulation⟩ := effect
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore status ⟨pc.val,false,_,retained,simulation,fun _ h=>h,rfl,fun _ h=>h⟩
  | ready point =>
    obtain ⟨count,g,labels,stop,types,chain,bound,represented,continuation,retained,metadata,done⟩ :=
      Machine.normalize_execution view code store exec raw index compiled C targets next output ambient f rest
        last hf program slots point expected machine
    have nextProgram : FrameProgram store raw compiled (g.locals.map Representation.valueType) g.resultTypes C.FUNCS := program.reposition raw.pc metadata
    rcases done with skip | ready
    · obtain ⟨target,forward,fetched,tail⟩ := skip
      apply Or.inr
      apply WP.spec_mono (Machine.step_forward_jump memory hooks floats allocator view code exec store platform index raw inst compiled
        ambient g rest expected C labels stop types target last hf hi hc forward fetched represented tail retained nextProgram)
      intro out effect
      have outcome := SupportedStepOutcome.unchanged_success (allocator:=allocator) (hooks:=hooks) (exec:=exec) (platform:=platform)
        shaped sourceSyntax bounds effect.2.1 effect.1
        ⟨target.val,false,_,effect.2.2.2.2.1,effect.2.2.2.2.2,fun _ h=>h,rfl,fun _ h=>h⟩
      exact outcome.prepend_normalization chain machine.typed.typed
    · have nextModule : g.module=Representation.decodeInstance store inst := metadata.module.trans moduleEq
      rcases step_ready_supported_host_site memory hooks floats allocator view laws code exec store platform index raw inst compiled
        C labels stop types ambient g rest last hf hi hc nextProgram represented nextModule small continuation expected retained ready shaped sourceSyntax bounds compiledFunctions functionTyping (chain.ownership.stateful owned) with host | operation
      · exact Or.inl (.normalize chain host)
      · apply Or.inr
        apply WP.spec_mono operation
        intro out outcome
        exact outcome.prepend_normalization chain machine.typed.typed

theorem step_supported_host_site
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (source : SourceMachine.AState) (expected : List valtype) (pc : Nat) (pending : Bool)
    (decoded : source.store = Representation.decodeStore view code store)
    (shaped : Representation.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store)
    (compiledFunctions : Machine.CompiledFunctions code store) (functionTyping : CoreFunctionsTyped view code store)
    (owned : SourceMachine.Ownership.StatefulOwned (Store.ownershipBounds store) source)
    (invariant : Machine.Execution view code store exec source expected pc pending)
    (active : 0 < exec.frames.length) :
    StructuredHostSite view code exec store expected pc pending source ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SupportedStepOutcome allocator hooks view code exec store platform expected U32.max pc pending source out ⦄ := by
  have small : ∀ object ∈ store.globals.val, object.ty.valtype=.I32 ∨ object.ty.valtype=.F32 → object.lo.val<2^32 := by
    intro object member ty
    have shape := shaped.globals object member
    rcases ty with ty | ty <;> simp only [Representation.GlobalShape,ty] at shape <;> exact shape.1
  rcases source with ⟨s, ambient, frames, results⟩
  cases frames with
  | nil =>
    have stack := invariant.stack
    cases stack with
    | empty empty => simp only [alloc.vec.Vec.length, empty, List.length_nil] at active; omega
  | cons f rest =>
    have noResults := invariant.typed.typed.activeResults (by simp)
    change results = [] at noResults
    subst results
    obtain ⟨raw, compiled, C, targets, next, output, top, position, program, point⟩ := invariant.cursor
    obtain ⟨inst, hi, hc, functionTable⟩ := program.lookup
    have bound : exec.frames.length - 1 ≤ Usize.max := (Nat.sub_le _ _).trans exec.frames.property
    have encoded : exec.frames.length - 1 < 2 ^ UScalarTy.Usize.numBits := by scalar_tac
    let index : Usize := UScalar.ofNatCore (exec.frames.length - 1) encoded
    have indexVal : index.val = exec.frames.length - 1 := UScalar.ofNatCore_val_eq encoded
    have last : index.val + 1 = exec.frames.length := by omega
    have hf : exec.frames.val[index.val]? = some raw := by
      rw [indexVal]
      simpa only [List.getLast?_eq_getElem?] using top
    have current := invariant.stack.top raw top
    have moduleEq := current.binding.module_lookup inst hi
    change s = Representation.decodeStore view code store at decoded
    subst s
    rcases step_frame_supported_host_site memory hooks floats allocator view laws code exec store platform
      index raw inst compiled C targets next output ambient f rest
      last hf hi hc program current.slots moduleEq small pending point expected (by simpa only [position] using invariant) shaped sourceSyntax bounds compiledFunctions functionTyping owned with host | operation
    · exact Or.inl (by simpa only [position] using host)
    · apply Or.inr
      apply WP.spec_mono operation
      intro out outcome
      simpa only [position] using outcome.widen program.fetchBound

end Itasca.Integration

end

end
