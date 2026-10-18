import Exec.Theorems.Api.ReadbackIssued
import Exec.Theorems.Host.HostCallRetained
import Exec.Interp.Invocation.InvokeRecordedPrefix
import Exec.Interp.Invocation.InvokeLoopRecordingFacts
import Exec.Theorems.Host.HostCallRecording
import Exec.Theorems.Composition.Core.CoreOwnership
import Exec.Store.Invariant.CheckedValues
import Exec.Theorems.Composition.Entry
import Exec.Theorems.Composition.Eventful.EventfulErrors
import Exec.Spec.HostCall
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- The initial host invocation records the actual callback reply. Both successful
readback and every error use this same returned log in their source execution. -/
theorem invoke_host_recorded_outcomes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (invariant : runtime.store.Store M → Prop)
    (shape : ∀ s, invariant s → Store.Shape view s)
    (sound : Platform.HostSound hooks invariant (Store.decodeStore view code))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : invariant store) (sourceWf : wf_store (Store.decodeStore view code store))
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.Function) (identity : U64)
    (signature : Itasca.types.FuncType) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (functionAt : store.funcs.val[address.index.val]? = some function)
    (host : function.code = .Host identity)
    (signatureAt : store.types.val[function.signature.val]? = some signature)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()))
    (preserve : ∀ p arguments defaults answer,
      hooks.call_host p store identity arguments defaults = .ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀ p arguments defaults answer,
      hooks.call_host p store identity arguments defaults = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length)
    (issued : ∀ p arguments defaults answer,
      hooks.call_host p store identity arguments defaults = .ok answer →
      ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value) :
    recordedInvokeWith memory hooks floats allocator exec store platform address args results [] ⦃ (out,trace) =>
      (invariant out.2.2.1 ∧ FrameStorePrefix store out.2.2.1 ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
        store.externs.length ≤ out.2.2.1.externs.length) ∧
      (out.1 = .Ok () →
        ResultsTyped (Store.decodeStore view code out.2.2.1) (signature.results.val.map sourceType)
          (out.2.2.2.2.val.map sourceValue) ∧
        Abs.Ownership.ValuesOwned (Store.ownershipBounds out.2.2.1) (out.2.2.2.2.val.map sourceValue) ∧
        StepsH ⟨⟨Store.decodeStore view code store,ambient⟩, vals (args.val.map sourceValue) ++ [.CALL_ADDR address.index.val]⟩
          trace
          ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩, vals (out.2.2.2.2.val.map sourceValue)⟩ ∧
        (∀ value ∈ out.2.2.2.2.val, Store.ValueInStore out.2.2.1 value)) ∧
      (∀ error, out.1 = .Err error → EventfulInvocationError
        ⟨⟨Store.decodeStore view code store,ambient⟩, vals (args.val.map sourceValue) ++ [.CALL_ADDR address.index.val]⟩
        trace (Store.decodeStore view code out.2.2.1) ambient error) ⦄ := by
  have arguments := checked_arguments_typed memory view code store sourceWf args signature.params accepted owned
  have initialWf := Spec.host_call_wf (fa:=address.index.val) sourceWf ambientWf arguments
  have argsOwned := Store.source_values_owned store args.val owned
  let retained := fun after => invariant after ∧ FrameStorePrefix store after ∧
    Extend_store (Store.decodeStore view code store) (Store.decodeStore view code after) ∧
    store.externs.length ≤ after.externs.length
  let property := fun after values trace =>
    ResultsTyped (Store.decodeStore view code after) (signature.results.val.map sourceType) values ∧
    Abs.Ownership.ValuesOwned (Store.ownershipBounds after) values ∧
    StepsH ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue) ++ [.CALL_ADDR address.index.val]⟩
      trace
      ⟨⟨Store.decodeStore view code after,ambient⟩,vals values⟩
  let errors := fun (after : runtime.store.Store M) (error : runtime.ExecError) (trace : List HostEvent) =>
    EventfulInvocationError
      ⟨⟨Store.decodeStore view code store,ambient⟩, vals (args.val.map sourceValue) ++ [.CALL_ADDR address.index.val]⟩
      trace (Store.decodeStore view code after) ambient error
  let entry := fun (after : runtime.store.Store M) (entered : runtime.interp.Execution) (trace : List HostEvent) => retained after ∧ entered.frames.val = [] ∧
    ∃ values, ValuesAt entered.slots.val 0 values ∧ property after values trace
  refine WP.spec_mono (recorded_invoke_with_prefix_owned_causes_composition_mode memory hooks floats allocator false allocation exec store platform
    address function signature args results [] owner functionAt signatureAt accepted
    (fun value member => (owned value member).1) entry retained
    ⟨valid,.refl _,Spec.extend_store_refl _ sourceWf,Nat.le_refl _⟩ property errors ?_ ?_ ?_ ?_) ?_
  · intro error cause
    cases error <;> try simp only [InvocationResourceCause] at cause
    rename_i limit
    exact ⟨_,StepsH.refl initialWf⟩
  · intro after values trace kept satisfied refused
    obtain ⟨typed,ownership,source⟩ := satisfied
    exact ⟨vals values,source⟩
  · intro prepared p executionId empty represented
    obtain ⟨called,actual,fresh,kept,extension,count,effect,causes⟩ := WP.spec_imp_exists
      (call_host_source_retained memory hooks floats allocator allocation interrupts view code invariant shape sound
        prepared store p valid address 0#usize ambient ambientWf function identity signature functionAt host signatureAt
        (args.val.map sourceValue) (by simpa only [show Code.valueType=Abs.valueType from funext valueType_eq_abs] using (Abs.results_type_of_typed arguments).symm) arguments
        (Spec.resultsTyped_wf arguments) (fun value member => Store.owned_result_fits store value (argsOwned value member))
        represented sourceWf preserve externs issued)
    have recorded := (recordedCall_returned memory hooks floats allocator prepared store p address 0#usize [] called (hostCallEvents address called)).mpr
      ⟨actual,by simp only [List.nil_append,callHostEvents_host functionAt host]⟩
    rw [recorded]
    simp only [WP.spec_ok]
    refine ⟨⟨fresh,kept,extension,count⟩,?_,?_⟩
    · intro success
      rcases effect with ⟨error,status,_,_⟩ | ⟨effect,typed⟩
      · rw [success] at status; cases status
      · obtain ⟨typed,ownedResults⟩ := typed success
        refine ⟨⟨fresh,kept,extension,count⟩,?_,called.2.1.host_results.val.map sourceValue,?_,typed,ownedResults,?_⟩
        · exact congrArg alloc.vec.Vec.val effect.2.1 |>.trans empty
        · rcases effect.2.2.2.2 with good | bad
          · exact good.2.1
          · rcases bad.1 with bad | bad <;> rw [success] at bad <;> cases bad
        · simpa only [hostCallResultConfig,success] using
            effect.events view code store ambient address (args.val.map sourceValue) 0#usize prepared called
    · intro error rejected
      change EventfulInvocationError _ (hostCallEvents address called) _ _ _
      rcases effect with ⟨early,status,cause,same⟩ | ⟨effect,typed⟩
      · have eq : early=error := by simpa only [rejected,core.result.Result.Err.injEq] using status.symm
        subst early
        have kind := cause.error
        cases error <;> simp only [HostPreparationError] at kind
        case Exhausted limit =>
          cases limit <;> simp only at kind
          all_goals simpa only [EventfulInvocationError,hostCallEvents,rejected,same] using
            (show ∃ body, StepsH ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue) ++ [.CALL_ADDR address.index.val]⟩ [] ⟨⟨Store.decodeStore view code store,ambient⟩,body⟩ from
              ⟨_,StepsH.refl initialWf⟩)
        case Terminated =>
          simpa only [EventfulInvocationError,hostCallEvents,rejected,same] using
            (show ∃ body, StepsH ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue) ++ [.CALL_ADDR address.index.val]⟩ [] ⟨⟨Store.decodeStore view code store,ambient⟩,body⟩ from
              ⟨_,StepsH.refl initialWf⟩)
      · have source := effect.events view code store ambient address (args.val.map sourceValue) 0#usize prepared called
        rcases effect.2.2.2.2 with good | bad
        · rw [rejected] at good
          cases good.1
        · obtain ⟨failure,_,footprint⟩ := bad
          rcases failure with trapped | exhausted
          · have eq : error=.Trap .Host := by simpa only [rejected,core.result.Result.Err.injEq] using trapped
            subst error
            simpa only [EventfulInvocationError,hostCallResultConfig,rejected] using source
          · have eq : error=.Exhausted .CallStack := by simpa only [rejected,core.result.Result.Err.injEq] using exhausted
            subst error
            refine ⟨[.TRAP],?_⟩
            simpa only [hostCallResultConfig,rejected] using source
  · intro after entered p trace enteredProof
    obtain ⟨kept,empty,values,represented,typed,ownedResults,source⟩ := enteredProof
    have stopped : ¬ActiveExecution (entered,after,p,.Ok ()) := by
      simp [ActiveExecution,empty,alloc.vec.Vec.length]
    simp only [InvocationWP]
    rw [recordedInvokeLoop_stopped memory hooks floats allocator (entered,after,p,.Ok ()) stopped trace]
    simp only [WP.spec_ok,finishExecution]
    exact ⟨kept.2.1,kept,fun _ => ⟨values,(by simpa only [show Code.valueType=Abs.valueType from funext valueType_eq_abs] using (Abs.results_type_of_typed typed).symm),Spec.resultsTyped_wf typed,
      fun value member => Store.owned_result_fits after value (ownedResults value member),represented,typed,ownedResults,source⟩,
      fun error impossible => by cases impossible⟩
  · rintro ⟨out,trace⟩ ⟨kept,success,errors⟩
    refine ⟨kept,?_,errors⟩
    intro accepted
    obtain ⟨⟨typed,ownedValues,source⟩,owners⟩ := success accepted
    exact ⟨typed,ownedValues,source,fun value member =>
      owned_source_value_in_store out.2.2.1 value (owners value member)
        (ownedValues (sourceValue value) (List.mem_map.mpr ⟨value,member,rfl⟩))⟩
end Exec.Theorems
