import Itasca.Runtime.Integration.Execution.Dispatch.Outcomes
import Itasca.Runtime.Integration.Execution.Resources.Failure
import Itasca.Runtime.Integration.Execution.Mutation.Operations
import Itasca.Runtime.Interp.Machine.Progress.SupportedAdvance
import Itasca.Runtime.Interp.Machine.Progress.UnreachableExecution
import Itasca.Runtime.SourceMachine.Float.Transition
import Itasca.Runtime.Interp.Machine.Control.BranchSource
import Itasca.Runtime.Interp.Machine.Normalization.IndexedEmpty
import Itasca.Runtime.Interp.Machine.Float.StructuredOwned
import Itasca.Runtime.Interp.Machine.Simd.Execution

/-!
Sections, each formerly its own module: UniformOutcomes, Scalar, Simd.
-/

/-! ## UniformOutcomes -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Itasca.Runtime.Interp
/-- Concrete mutation evidence and the full source/machine outcome of one
cumulative dispatch. Fresh certification follows from the mutation witness. -/
def UniformSupportedStepOutcome {M P A : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (expected : List valtype) (codeLength pc : Nat) (pending : Bool) (source : SourceMachine.AState)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : Prop :=
  CumulativeStoreMutation view code store out.2.2.1 ∧
    match out.1 with
    | .Ok _ => Machine.UniformAdvance view code out.2.2.1 out.2.1 expected codeLength pc pending source
    | .Err error => CumulativeFailure allocator hooks exec store platform source error ∧
      Store.decodeStore view code out.2.2.1=source.store

variable {M P A : Type} {allocator : runtime.platform.Alloc A} {hooks : runtime.platform.Platform P M}
  {view : M → Slice U8} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
  {store : runtime.store.Store M} {platform : P} {expected : List valtype}
  {codeLength pc : Nat} {pending : Bool} {source : SourceMachine.AState}
  {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}

theorem UniformSupportedStepOutcome.success (mutation : CumulativeStoreMutation view code store out.2.2.1)
    (status : out.1=.Ok ())
    (advance : Machine.UniformAdvance view code out.2.2.1 out.2.1 expected codeLength pc pending source) :
    UniformSupportedStepOutcome allocator hooks view code exec store platform expected codeLength pc pending source out :=
  ⟨mutation,by simpa only [status] using advance⟩

theorem UniformSupportedStepOutcome.unchanged_success (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store)
    (same : out.2.2.1=store) (status : out.1=.Ok ())
    (advance : Machine.UniformAdvance view code store out.2.1 expected codeLength pc pending source) :
    UniformSupportedStepOutcome allocator hooks view code exec store platform expected codeLength pc pending source out := by
  apply UniformSupportedStepOutcome.success (by rw [same]; exact .refl_of_shape shaped sourceSyntax bounds) status
  simpa only [same] using advance

theorem UniformSupportedStepOutcome.failure (mutation : CumulativeStoreMutation view code store out.2.2.1)
    {error : runtime.ExecError} (status : out.1=.Err error)
    (decoded : Store.decodeStore view code out.2.2.1=source.store)
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
end Itasca.Runtime.Integration

end

/-! ## Scalar -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt SourceMachine.Float Itasca.Runtime.Interp

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
    (next : Nat) (output : List valtype) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (op : Instruction) (after : List instr)
    (last : index.val+1 = exec.frames.length) (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : Machine.FramePoint (Store.decodeStore view code store) raw {f with code := op.source::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Machine.Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩
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
    C targets next output (Store.decodeStore view code store) ambient f rest op after last frameFound instanceFound codeFound
    pcBound machine.typed.typed slots point)
  intro out effect
  obtain ⟨sameStore,samePlatform,operation⟩ := effect
  refine ⟨sameStore,samePlatform,?_⟩
  rcases operation with ⟨success,pc,g,fields,represented,retained,typed,metadata,simulation,prefixEffect,owned,transition⟩ |
    ⟨trap,failed,kind,count,positive,source⟩
  · have uniform : UniformConcreteSim raw.pc.val pc.val false false
        ⟨Store.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩
        ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ [] := by
      rcases transition with same | actual
      · subst g
        exact simulation.uniform_same (by scalar_tac)
      · exact UniformConcreteSim.single (SourceMachine.Float.transition_positive _ _ _ _ _ _ _ machine.typed.typed actual)
    have facts : SourceMachine.CoreTyped ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ ∧
        SourceMachine.SupportedState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds ⟨Store.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩ →
          SourceMachine.Ownership.StatefulOwned bounds ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩) ∧
        (∀ bound, SourceMachine.CodeBound bound ⟨Store.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩ →
          SourceMachine.CodeBound bound ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩) := by
      rcases transition with same | actual
      · subst g
        exact ⟨machine.typed,machine.core,fun _ owned => owned,fun _ bounded => bounded⟩
      · have step : SourceMachine.Cumulative.Step ⟨Store.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩
            (.next ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩) := .scalar actual
        exact ⟨step.next_typed_supported machine.typed machine.core,step.next_covered_supported machine.typed machine.core,
          fun _ invariant => step.next_owned_supported machine.typed machine.core invariant,
          fun _ invariant => step.next_bound_supported machine.typed machine.core invariant⟩
    have fresh := Machine.Execution.ordinary view code ambient {f with code := op.source::after} g rest expected raw.pc.val false machine
      (.refl store) (Itasca.Runtime.Spec.extend_store_refl _ machine.typed.typed.store) raw index pc last frameFound program
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
    (next : Nat) (output : List valtype) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (op : Instruction) (after : List instr)
    (last : index.val+1 = exec.frames.length) (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : Machine.FramePoint (Store.decodeStore view code store) raw {f with code := op.source::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Machine.Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      SupportedStepOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false initial out ⦄ := by
  apply WP.spec_mono (step_scalar_supported_execution_uniform memory hooks floats allocator correct exec store platform index raw inst compiled C targets next output view code ambient f rest op after last frameFound instanceFound codeFound slots point expected machine program shaped sourceSyntax bounds)
  rintro out ⟨same,platform,outcome⟩
  exact ⟨same,platform,outcome.forget⟩

end Itasca.Runtime.Integration

end

/-! ## Simd -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Itasca.Runtime.Interp
theorem step_simd_supported_execution {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (interpretation : Store.CodeInterpretation)
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
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : Machine.FramePoint (Store.decodeStore view interpretation store) raw
      {f with code:=source::after} compiled C targets next output)
    (simd : SourceMachine.SimdInstr source)
    (machine : Machine.Execution view interpretation store exec
      ⟨Store.decodeStore view interpretation store,ambient,{f with code:=source::after}::rest,[]⟩ expected raw.pc.val false)
    (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax interpretation store)
    (bounds : Store.SegmentBounds store) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SupportedStepOutcome allocator hooks view interpretation exec store platform expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view interpretation store,ambient,{f with code:=source::after}::rest,[]⟩ out ⦄ := by
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
end Itasca.Runtime.Integration

end
