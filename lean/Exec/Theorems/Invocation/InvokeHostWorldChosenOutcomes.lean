import Exec.Theorems.Api.ReadbackIssued
import Exec.Theorems.Host.Chosen.HostCallChosenWorld
import Exec.Theorems.Composition.Eventful.ChosenEventfulErrors
import Exec.Interp.Invocation.InvokePrefixCauses
import Exec.Theorems.Composition.Core.CoreOwnership
import Exec.Store.Invariant.CheckedValues
import Exec.Theorems.Composition.Entry
import Exec.Theorems.Composition.Eventful.EventfulErrors
import Exec.Spec.HostCall
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem invoke_host_world_chosen_outcomes {choices : Spec.SourceChoices} (admissible : choices.Admissible) (occurrence : Nat) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (invariant : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (shape : ∀ c s, invariant c s → Store.Shape view s)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : invariant code store) (sourceWf : wf_store (Store.decodeStore view code store))
    (entryTyped : Store_ok (Store.decodeStore view code store))
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (identity : U64)
    (signature : Itasca.types.FuncType) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (functionAt : store.funcs.val[address.index.val]? = some function)
    (host : function.code = .Host identity)
    (signatureAt : store.types.val[function.signature.val]? = some signature)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()))
    (callback : ∀ p arguments defaults,
      hooks.call_host p store identity arguments defaults ⦃ answer => ∃ afterCode,
        Store.CodeAgreesOn store code afterCode ∧ invariant afterCode answer.2.2.1 ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode answer.2.2.1) ∧
        Store_ok (Store.decodeStore view afterCode answer.2.2.1) ∧
        choices.host occurrence (Store.decodeStore view code store) address.index.val identity.val
          (signature.params.val.map sourceType) (signature.results.val.map sourceType) (arguments.val.map sourceValue)=
          checkedHostReply memory view afterCode answer.2.2.1 signature ⟨answer.2.2.2⟩ answer.1 ⦄)
    (preserve : ∀ p arguments defaults answer,
      hooks.call_host p store identity arguments defaults = .ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀ p arguments defaults answer,
      hooks.call_host p store identity arguments defaults = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length)
    (issued : ∀ p arguments defaults answer,
      hooks.call_host p store identity arguments defaults = .ok answer →
      ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results ⦃ out => ∃ afterCode,
      (invariant afterCode out.2.2.1 ∧ Store.CodeAgreesOn store code afterCode ∧ FrameStorePrefix store out.2.2.1 ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode out.2.2.1) ∧
        store.externs.length ≤ out.2.2.1.externs.length) ∧
      (out.1 = .Ok () →
        ResultsTyped (Store.decodeStore view afterCode out.2.2.1) (signature.results.val.map sourceType)
          (out.2.2.2.2.val.map sourceValue) ∧
        Abs.Ownership.ValuesOwned (Store.ownershipBounds out.2.2.1) (out.2.2.2.2.val.map sourceValue) ∧
        Spec.ChoiceStep choices occurrence ⟨⟨Store.decodeStore view code store,ambient⟩, vals (args.val.map sourceValue) ++ [.CALL_ADDR address.index.val]⟩
          [.call address.index.val (args.val.map sourceValue) (some (out.2.2.2.2.val.map sourceValue))]
          ⟨⟨Store.decodeStore view afterCode out.2.2.1,ambient⟩, vals (out.2.2.2.2.val.map sourceValue)⟩ ∧
        (∀ value ∈ out.2.2.2.2.val, Store.ValueInStore out.2.2.1 value)) ∧
      (∀ error, out.1 = .Err error → ∃ events, ChosenEventfulInvocationError choices occurrence
        ⟨⟨Store.decodeStore view code store,ambient⟩, vals (args.val.map sourceValue) ++ [.CALL_ADDR address.index.val]⟩
        events (Store.decodeStore view afterCode out.2.2.1) ambient error) ⦄ := by
  have arguments := checked_arguments_typed memory view code store sourceWf args signature.params accepted owned
  have initialWf := Spec.host_call_wf (fa:=address.index.val) sourceWf ambientWf arguments
  have argsOwned := Store.source_values_owned store args.val owned
  let retained := fun after => FrameStorePrefix store after ∧ store.externs.length ≤ after.externs.length
  let property := fun after values => ∃ afterCode,
    invariant afterCode after ∧ Store.CodeAgreesOn store code afterCode ∧
    Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode after) ∧
    ResultsTyped (Store.decodeStore view afterCode after) (signature.results.val.map sourceType) values ∧
    Abs.Ownership.ValuesOwned (Store.ownershipBounds after) values ∧
    Spec.ChoiceStep choices occurrence ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue) ++ [.CALL_ADDR address.index.val]⟩
      [.call address.index.val (args.val.map sourceValue) (some values)]
      ⟨⟨Store.decodeStore view afterCode after,ambient⟩,vals values⟩
  let errors := fun (after : runtime.store.Store M) (error : runtime.ExecError) => ∃ afterCode,
    invariant afterCode after ∧ Store.CodeAgreesOn store code afterCode ∧
    Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode after) ∧
    ∃ events, ChosenEventfulInvocationError choices occurrence
      ⟨⟨Store.decodeStore view code store,ambient⟩, vals (args.val.map sourceValue) ++ [.CALL_ADDR address.index.val]⟩
      events (Store.decodeStore view afterCode after) ambient error
  let entry := fun (after : runtime.store.Store M) (entered : runtime.interp.Execution) => retained after ∧ entered.frames.val = [] ∧
    ∃ values, ValuesAt entered.slots.val 0 values ∧ property after values
  refine WP.spec_mono (invoke_with_prefix_owned_causes_composition_mode memory hooks floats allocator false allocation exec store platform
    address function signature args results owner functionAt signatureAt accepted
    (fun value member => (owned value member).1) entry retained
    ⟨.refl _,Nat.le_refl _⟩ property errors ?_ ?_ ?_ ?_) ?_
  · intro error cause
    refine ⟨code,valid,(by intro index inst found fn; rfl),Spec.extend_store_refl _ sourceWf,?_⟩
    cases error <;> try simp only [InvocationResourceCause] at cause
    rename_i limit
    exact ⟨[],_,0,Spec.ChosenStepsN.refl occurrence initialWf⟩
  · intro after values kept satisfied refused
    obtain ⟨afterCode,fresh,agrees,extension,typed,ownership,source⟩ := satisfied
    exact ⟨afterCode,fresh,agrees,extension,[.call address.index.val (args.val.map sourceValue) (some values)], vals values,
      1,by simpa only [List.append_nil] using Spec.ChosenStepsN.cons source (Spec.ChosenStepsN.refl (occurrence+1) (source.wf admissible).2)⟩
  · intro prepared p executionId empty represented
    obtain ⟨called,actual,afterCode,agrees,fresh,kept,extension,count,effect,causes⟩ := WP.spec_imp_exists
      (call_host_chosen_retained_world (choices:=choices) occurrence memory hooks floats allocator allocation interrupts view code invariant shape
        prepared store p valid address 0#usize ambient ambientWf function identity signature functionAt host signatureAt
        (args.val.map sourceValue) (by simpa only [show Code.valueType=Abs.valueType from funext valueType_eq_abs] using (Abs.results_type_of_typed arguments).symm) arguments
        (Spec.resultsTyped_wf arguments) (fun value member => Store.owned_result_fits store value (argsOwned value member))
        represented sourceWf entryTyped callback preserve externs issued)
    have sameDecode := Store.decodeStore_code_agrees view agrees
    rw [actual]
    simp only [WP.spec_ok]
    refine ⟨⟨kept,count⟩,?_,?_⟩
    · intro success
      rcases effect with ⟨error,status,_,_⟩ | ⟨effect,typed⟩
      · rw [success] at status; cases status
      · obtain ⟨typed,ownedResults⟩ := typed success
        refine ⟨⟨kept,count⟩,?_,called.2.1.host_results.val.map sourceValue,?_,afterCode,fresh,agrees,extension,typed,ownedResults,?_⟩
        · exact congrArg alloc.vec.Vec.val effect.2.1 |>.trans empty
        · rcases effect.2.2.2.2 with good | bad
          · exact good.2.1
          · rcases bad.1 with bad | bad <;> rw [success] at bad <;> cases bad
        · rcases effect.2.2.2.2 with good | bad
          · simpa only [sameDecode] using good.2.2.1
          · rcases bad.1 with bad | bad <;> rw [success] at bad <;> cases bad
    · intro error rejected
      refine ⟨afterCode,fresh,agrees,extension,?_⟩
      rcases effect with ⟨early,status,cause,same⟩ | ⟨effect,typed⟩
      · have eq : early=error := by simpa only [rejected,core.result.Result.Err.injEq] using status.symm
        subst early
        rw [same,sameDecode]
        have kind := cause.error
        cases error <;> first
          | exact ⟨[],_,0,Spec.ChosenStepsN.refl occurrence initialWf⟩
          | simp [HostPreparationError] at kind
      · rcases effect.2.2.2.2 with good | bad
        · rw [rejected] at good
          cases good.1
        · obtain ⟨failure,source,footprint⟩ := bad
          have trace := Spec.ChosenStepsN.cons source (Spec.ChosenStepsN.refl (occurrence+1) (source.wf admissible).2)
          rw [sameDecode] at trace
          rcases failure with trapped | exhausted
          · have eq : error=.Trap .Host := by simpa only [rejected,core.result.Result.Err.injEq] using trapped
            subst error
            exact ⟨[.call address.index.val (args.val.map sourceValue) none],1,by simpa only [List.append_nil] using trace⟩
          · have eq : error=.Exhausted .CallStack := by simpa only [rejected,core.result.Result.Err.injEq] using exhausted
            subst error
            exact ⟨[.call address.index.val (args.val.map sourceValue) none],[.TRAP],1,by simpa only [List.append_nil] using trace⟩
  · intro after entered p enteredProof
    obtain ⟨kept,empty,values,represented,afterCode,fresh,agrees,extension,typed,ownedResults,source⟩ := enteredProof
    have stopped : ¬0#usize < entered.frames.len := by simp [alloc.vec.Vec.len,empty,alloc.vec.Vec.length]
    simp only [InvocationWP,ite_false]
    simp only [runtime.interp.invoke_with_loop1]
    apply loop.spec_decr_nat (fun _ => 0) (fun state => state = (entered,after,p,.Ok ()))
    · rintro state rfl
      simp only [runtime.interp.invoke_with_loop1.body,stopped,ite_false,WP.spec_ok]
      exact ⟨kept.1,kept,fun _ => ⟨values,(by simpa only [show Code.valueType=Abs.valueType from funext valueType_eq_abs] using (Abs.results_type_of_typed typed).symm),Spec.resultsTyped_wf typed,
        fun value member => Store.owned_result_fits after value (ownedResults value member),represented,afterCode,fresh,agrees,extension,typed,ownedResults,source⟩,
        fun error impossible => by cases impossible⟩
    · rfl
  · rintro out ⟨kept,success,errors⟩
    cases status : out.1 with
    | Ok unit =>
      cases unit
      obtain ⟨⟨afterCode,fresh,agrees,extension,typed,ownedValues,source⟩,owners⟩ := success status
      refine ⟨afterCode,⟨fresh,agrees,kept.1,extension,kept.2⟩,?_,?_⟩
      · intro _
        exact ⟨typed,ownedValues,source,fun value member =>
          owned_source_value_in_store out.2.2.1 value (owners value member)
            (ownedValues (sourceValue value) (List.mem_map.mpr ⟨value,member,rfl⟩))⟩
      · intro error impossible
        cases impossible
    | Err error =>
      obtain ⟨afterCode,fresh,agrees,extension,events,source⟩ := errors error status
      refine ⟨afterCode,⟨fresh,agrees,kept.1,extension,kept.2⟩,?_,?_⟩
      · intro impossible
        cases impossible
      · intro reported failed
        have equal : error=reported := by simpa only [core.result.Result.Err.injEq] using failed
        subst reported
        exact ⟨events,source⟩
end Exec.Theorems
