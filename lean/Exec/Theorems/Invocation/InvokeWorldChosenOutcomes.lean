import Exec.Theorems.Composition.World.ChosenWorldTotal
import Exec.Theorems.Composition.World.ChosenWorldLoopResult
import Exec.Spec.Choices.NeutralStep
import Exec.Theorems.Composition.Eventful.EventfulWorldLoop
import Exec.Theorems.Composition.Supported.SupportedEntryOutcomes
import Exec.Interp.Invocation.InvokePrefixCauses
import Exec.Theorems.Api.ReadbackIssued
import Exec.Spec.HostCall
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Actual public defined-function invocation keeps one selected final code
world with its invariant, source outcomes and issued readback values. -/
theorem invoke_defined_world_chosen_outcomes {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Spec.firstNumericChoice) (vector : choices.vector=Spec.firstVectorChoice) (occurrence : Nat)
    [∀ compiled, StructuredMachine.FloatHeads (emission compiled)]
    [∀ compiled, StructuredMachine.OrdinaryHeads (emission compiled)]
    [∀ compiled, StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.IndirectProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.SimdProjection (emission compiled) compiled.simd.val compiled.v128_pool.val]
    [∀ compiled, StructuredMachine.TypedSelectHeads (emission compiled)]
    [∀ compiled, StructuredMachine.SupportedHeads (emission compiled)]
    [∀ compiled, StructuredMachine.ErasedHeads (emission compiled)]
    [∀ compiled, StructuredMachine.RecordingHeads (emission compiled)]
    (language : Abs.Supported.Language allowed) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀ c s,Inv c s → CertifiedSupportedStore emission allowed view c s)
    (update : ∀ c before after,Inv c before → CumulativeStoreMutation view c before after → Inv c after)
    (typedStore : ∀ code store,Inv code store → Store_ok (Store.decodeStore view code store))
    (sound : HostWorldChosenSound memory hooks view Inv choices)
    (preserve : ∀ c store, Inv c store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀ c store, Inv c store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀ c store, Inv c store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer →
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv code store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ())) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ∃ afterCode,
        Inv afterCode out.2.2.1 ∧ FrameStorePrefix store out.2.2.1 ∧ Store.CodeAgreesOn store code afterCode ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode out.2.2.1) ∧
        (out.1=.Ok () →
          ResultsTyped (Store.decodeStore view afterCode out.2.2.1) (signature.results.val.map sourceType)
            (out.2.2.2.2.val.map sourceValue) ∧
          Abs.Ownership.ValuesOwned (Store.ownershipBounds out.2.2.1) (out.2.2.2.2.val.map sourceValue) ∧
          (∃events,Spec.ChoiceSteps choices occurrence ⟨⟨Store.decodeStore view code store,ambient⟩,
            vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ events
            ⟨⟨Store.decodeStore view afterCode out.2.2.1,ambient⟩,vals (out.2.2.2.2.val.map sourceValue)⟩) ∧
          (∀value∈out.2.2.2.2.val,Store.ValueInStore out.2.2.1 value)) ∧
        (∀error,out.1=.Err error → ∃events,ChosenEventfulInvocationError choices occurrence
          ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩
          events (Store.decodeStore view afterCode out.2.2.1) ambient error) ⦄div := by
  have certified := certify code store valid
  have storeWf := Store.decodeStore_wf view code store certified.shape certified.storeSyntax
  have arguments := checked_arguments_typed memory view code store storeWf args signature.params accepted owned
  have initialWf := Spec.host_call_wf (fa:=address.index.val) storeWf ambientWf arguments
  let retained := fun after => FrameStorePrefix store after
  let property := fun after values => ∃ afterCode,
    Inv afterCode after ∧ Store.CodeAgreesOn store code afterCode ∧
    Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode after) ∧
    ResultsTyped (Store.decodeStore view afterCode after) (signature.results.val.map sourceType) values ∧
    Abs.Ownership.ValuesOwned (Store.ownershipBounds after) values ∧
    ∃events,Spec.ChoiceSteps choices occurrence ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ events
      ⟨⟨Store.decodeStore view afterCode after,ambient⟩,vals values⟩
  let errors := fun after error => ∃ afterCode,
    Inv afterCode after ∧ Store.CodeAgreesOn store code afterCode ∧
    Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode after) ∧
    ∃events,ChosenEventfulInvocationError choices occurrence
      ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩
      events (Store.decodeStore view afterCode after) ambient error
  let entry := fun (after : runtime.store.Store M) (prepared : runtime.interp.Execution) => after=store ∧ ∃source,
    StructuredMachine.Execution emission (Abs.SupportedState allowed) view code store prepared source
      (signature.results.val.map sourceType) 0 false ∧
    Abs.Ownership.StatefulOwned (Store.ownershipBounds store) source ∧ source.ambient=ambient ∧
    StepH ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ [] (Abs.decode source)
  refine WP.dspec_mono (invoke_with_prefix_owned_causes_composition_mode memory hooks floats allocator true allocation exec store platform
    address function signature args results owner hf hs accepted (fun value member=>(owned value member).1)
    entry retained (.refl _) property errors ?_ ?_ ?_ ?_) ?_
  · intro error cause
    refine ⟨code,valid,(by intro index inst found fn; rfl),Spec.extend_store_refl _ storeWf,?_⟩
    cases error <;> try simp only [InvocationResourceCause] at cause
    rename_i limit
    exact ⟨[],_,0,Spec.ChosenStepsN.refl occurrence initialWf⟩
  · intro after values kept satisfied refused
    obtain ⟨afterCode,fresh,agrees,extension,typed,ownership,events,reductions⟩ := satisfied
    obtain ⟨count,counted⟩ := reductions.counted
    exact ⟨afterCode,fresh,agrees,extension,events,vals values,count,counted⟩
  · intro prepared p identity empty represented
    apply WP.spec_mono (call_defined_supported_entry_outcomes memory hooks floats allocator allocation interrupts view code
      prepared store p certified.shape certified.storeSyntax certified.segmentBounds certified.typed certified.supported certified.compiled
      ambient ambientWf address function signature instanceIndex functionIndex args empty identity represented accepted owned hf hs hw)
    intro out outcome
    refine ⟨?_,?_,?_⟩
    · simpa only [outcome.1] using (show retained store from .refl _)
    · intro success
      exact ⟨outcome.1,outcome.2.1 success⟩
    · intro error failed
      obtain ⟨inst,compiled,hi,hc,cause⟩ := outcome.2.2 error failed
      change ∃ afterCode, Inv afterCode _ ∧ Store.CodeAgreesOn store code afterCode ∧
        Extend_store _ _ ∧ ∃events,ChosenEventfulInvocationError choices occurrence _ events _ _ _
      rw [outcome.1]
      refine ⟨code,valid,(by intro index inst found fn; rfl),Spec.extend_store_refl _ storeWf,?_⟩
      rcases cause.kind with rfl | rfl | rfl | rfl <;> exact ⟨[],_,0,Spec.ChosenStepsN.refl occurrence initialWf⟩
  · intro after prepared p entered
    obtain ⟨same,source,invariant,ownedSource,ambientEq,sourceStep⟩ := entered
    subst after
    let machine : ChosenWorld emission allowed M P view (signature.results.val.map sourceType) :=
      ⟨⟨code,⟨store,prepared,p,source,0,false,invariant,certified,ownedSource⟩⟩,occurrence+1⟩
    apply WP.dspec_mono (chosen_world_loop_stops memory hooks floats allocator Inv
      (chosen_world_step_outcomes admissible numericChoice vector language memory hooks floats allocator correct allocation interrupts
        view laws compatible Inv certify update typedStore sound preserve externs issued _) machine valid)
    rintro out ⟨state,held,stopped,rfl⟩
    have outcome := chosen_world_loop_finished memory hooks floats allocator Inv machine state held stopped
    obtain ⟨afterCode,newValid,fresh,kept,agrees,extension,success,failed⟩ := outcome
    have chosenEntry := Spec.stepH_neutral_chosen admissible vector occurrence sourceStep (by
      simp only [Spec.trapCode,Spec.neutralActive_vals,Spec.neutralActive])
    refine ⟨kept,kept,?_,?_⟩
    · intro status
      obtain ⟨values,events,typed,ownedValues,represented,count,reductions⟩ := success status
      have tags : signature.results.val.map sourceType=values.map Code.valueType := by
        simpa only [show Code.valueType=Abs.valueType from funext valueType_eq_abs] using (Abs.results_type_of_typed typed).symm
      refine ⟨values,tags,Spec.resultsTyped_wf typed,?_,represented,afterCode,newValid,agrees,extension,typed,ownedValues,events,?_⟩
      · intro value member
        exact Store.owned_result_fits _ value (ownedValues value member)
      · simpa only [machine,ambientEq,List.nil_append,finishExecution] using Spec.ChoiceSteps.cons chosenEntry reductions.erase_count
    · intro error status
      obtain ⟨events,errorSource⟩ := failed error status
      refine ⟨afterCode,newValid,agrees,extension,events,?_⟩
      have first : Spec.ChosenStepsN choices occurrence 1
          ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ [] (Abs.decode source) := by
        simpa only [List.nil_append] using Spec.ChosenStepsN.cons chosenEntry (Spec.ChosenStepsN.refl (occurrence+1) invariant.typed.typed.decode_wf)
      simpa only [machine,ambientEq,List.nil_append,finishExecution] using errorSource.prepend first
  · intro out outcome
    cases status : out.1 with
    | Ok unit =>
      cases unit
      obtain ⟨⟨afterCode,fresh,agrees,extension,typed,sourceOwned,events,reductions⟩,rawOwned⟩ := outcome.2.1 status
      refine ⟨afterCode,fresh,outcome.1,agrees,extension,?_,?_⟩
      · intro _
        refine ⟨typed,sourceOwned,⟨events,reductions⟩,?_⟩
        intro value member
        apply owned_source_value_in_store out.2.2.1 value (rawOwned value member)
        exact sourceOwned _ (List.mem_map.mpr ⟨value,member,rfl⟩)
      · intro error failed
        cases failed
    | Err error =>
      obtain ⟨afterCode,fresh,agrees,extension,events,reductions⟩ := outcome.2.2 error status
      refine ⟨afterCode,fresh,outcome.1,agrees,extension,?_,?_⟩
      · intro success
        cases success
      · intro reported failed
        have equal : error=reported := by simpa only [status,core.result.Result.Err.injEq] using failed
        subst reported
        exact ⟨events,reductions⟩
end Exec.Theorems
