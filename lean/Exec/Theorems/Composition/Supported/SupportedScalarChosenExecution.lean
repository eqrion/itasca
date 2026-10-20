import Exec.Abs.Float.Positive
import Exec.Interp.Machines.Uniform.UniformSourceControl
import Exec.Theorems.Composition.Uniform.UniformSupportedOutcome
import Exec.Interp.StructuredMachine.IndexedLinear
import Exec.Interp.StructuredMachine.FloatChosenStructuredOwned
import Exec.Theorems.Composition.Supported.ChosenSupportedOutcome
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Abs.Float Exec.Interp

/-- All seventy scalar float operators preserve the mutable float machine or
return the exact generated arithmetic trap; allowed NaN choices remain relational. -/
theorem step_scalar_supported_chosen_execution {choices : Exec.Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Exec.Spec.firstNumericChoice) (occurrence : Nat) {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
    [∀ compiled, StructuredMachine.FloatHeads (emission compiled)]
    [∀ compiled, StructuredMachine.OrdinaryHeads (emission compiled)]
    (language : Abs.Supported.Language allowed) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.Instance)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (op : Instruction) (after : List instr)
    (last : index.val+1 = exec.frames.length) (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : StructuredMachine.FramePoint emission (Store.decodeStore view code store) raw {f with code := op.source::after} compiled C targets next output)
    (expected : List valtype)
    (machine : StructuredMachine.Execution emission (Abs.SupportedState allowed) view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ChosenSupportedStepOutcome choices occurrence emission allowed allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false initial out ⦄ := by
  dsimp only
  have pcBound : raw.pc.val < U32.max := by
    have linear : linearSource op.source = true := by cases op <;> rfl
    rcases StructuredMachine.structuredCodeWithTables_linear_inv linear point.code.current with skip | branch
    · obtain ⟨target,forward,fetched,continuation⟩ := skip
      have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have cap := program.fetchBound
      omega
    · obtain ⟨middle,emitted,tail,head,fragment,continuation⟩ := branch
      obtain ⟨stack,left,right,shape,middleEq,emittedEq,leftPos,rightPos⟩ := (StructuredMachine.FloatHeads.project (.scalar op) head).float_inv op
      have fetched : compiled.code.val[raw.pc.val]? = some (Code.floatInstruction op left left right) := by
        simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq,List.getElem?_cons_zero])
      have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have cap := program.fetchBound
      omega
  apply WP.spec_mono (StructuredMachine.step_float_chosen_structured_owned admissible numericChoice occurrence memory hooks floats allocator correct exec store platform index raw inst compiled
    C targets next output (Store.decodeStore view code store) ambient f rest op after last frameFound instanceFound codeFound
    pcBound machine.typed.typed slots point)
  intro out effect
  obtain ⟨sameStore,samePlatform,operation⟩ := effect
  refine ⟨sameStore,samePlatform,?_⟩
  rcases operation with ⟨success,pc,g,fields,represented,retained,typed,metadata,simulation,prefixEffect,owned,transition⟩ |
    ⟨trap,failed,kind,count,positive,source⟩
  · have facts : Abs.CoreTyped ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ ∧
        Abs.SupportedState allowed ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ ∧
        (∀ bounds, Abs.Ownership.StatefulOwned bounds ⟨Store.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩ →
          Abs.Ownership.StatefulOwned bounds ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩) ∧
        (∀ bound, Abs.CodeBound bound ⟨Store.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩ →
          Abs.CodeBound bound ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩) := by
      rcases transition with same | actual
      · subst g
        exact ⟨machine.typed,machine.core,fun _ owned => owned,fun _ bounded => bounded⟩
      · have step : Abs.Cumulative.Step ⟨Store.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩
            (.next ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩) := .scalar (actual.erases admissible)
        exact ⟨step.next_typed_supported language machine.typed machine.core,step.next_covered_supported language machine.typed machine.core,
          fun _ invariant => step.next_owned_supported language machine.typed machine.core invariant,
          fun _ invariant => step.next_bound_supported language machine.typed machine.core invariant⟩
    have fresh := StructuredMachine.Execution.ordinary view code ambient {f with code := op.source::after} g rest expected raw.pc.val false machine
      (.refl store) (Exec.Spec.extend_store_refl _ machine.typed.typed.store) raw index pc last frameFound program
      (.ready retained) represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ fields prefixEffect facts.1 facts.2.1
    exact ChosenSupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore success
      ⟨pc.val,false,_,fresh,simulation,facts.2.2.1,rfl,facts.2.2.2⟩
  · apply ChosenSupportedStepOutcome.failure (by rw [sameStore]; exact .refl_of_shape shaped sourceSyntax bounds) failed (by rw [sameStore])
    apply Or.inl
    refine ⟨⟨trap,rfl,Or.inl ?_⟩,count,positive,source⟩
    rcases kind with overflow | conversion
    · exact Or.inr (Or.inr (Or.inl overflow))
    · exact Or.inr (Or.inr (Or.inr (Or.inr conversion)))
end Exec.Theorems
