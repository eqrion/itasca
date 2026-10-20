import Exec.Theorems.Invocation.InvokeHostWorldChosenRecorded
import Exec.Theorems.Invocation.InvokeHostWorldResources
import Exec.Theorems.Api.InitialHostResourcesAdequate
import Exec.Interp.Invocation.InvokeRecordingErasure
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
/-- An issued host invocation matches the selected terminal source run, including
its exact recorder events and committed final store. Results are still checked
dynamically and resource failures have independent primitive exclusions. -/
theorem invoke_host_world_chosen_matches {choices : Spec.SourceChoices} (admissible : choices.Admissible) (occurrence : Nat) {M P F A : Type}
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
    (address : runtime.FuncAddr) (function : runtime.store.Function) (identity : U64)
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
      ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value)
    (typedStore : ∀c store,invariant c store → Store_ok (Store.decodeStore view c store))
    (signatureFits : signatureWords (Store.decodeFuncType signature)≤store.limits.max_values.val)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after))
    (overflow : ∀p arguments defaults nextPlatform after returned,
      hooks.call_host p store identity arguments defaults≠.ok (.Err .StackOverflow,nextPlatform,after,returned))
    {events : List HostEvent} {target : config}
    (run : Spec.ChoiceSteps choices occurrence
      ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ events target)
    (terminal : Spec.SourceTerminal target) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ∃afterCode,invariant afterCode out.2.2.1 ∧ Store_ok (Store.decodeStore view afterCode out.2.2.1) ∧
        FrameStorePrefix store out.2.2.1 ∧ Store.CodeAgreesOn store code afterCode ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode out.2.2.1) ∧
        recordedInvokeWith memory hooks floats allocator exec store platform address args results []=.ok (out,events) ∧
        match out.1 with
        | .Ok _ => target=⟨⟨Store.decodeStore view afterCode out.2.2.1,ambient⟩,vals (out.2.2.2.2.val.map sourceValue)⟩ ∧
            (∀value∈out.2.2.2.2.val,Store.ValueInStore out.2.2.1 value)
        | .Err (.Trap _) => target=⟨⟨Store.decodeStore view afterCode out.2.2.1,ambient⟩,[.TRAP]⟩
        | .Err _ => False ⦄ := by
  obtain ⟨⟨out,nativeEvents⟩,graph,afterCode,⟨fresh,agrees,kept,extension,count⟩,success,failure⟩ := WP.spec_imp_exists
    (invoke_host_world_chosen_recorded_outcomes admissible occurrence memory hooks floats allocator allocation interrupts view code invariant shape
      exec store platform valid sourceWf entryTyped ambient ambientWf address function identity signature args results owner functionAt host signatureAt
      owned accepted callback preserve externs issued)
  have actual : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results=.ok out := by
    have erased := recordedInvokeWith_erase memory hooks floats allocator exec store platform address args results []
    simpa [graph,bind_ok] using erased.symm
  have bounded := invoke_host_world_recorded_resources memory hooks floats allocator allocation interrupts view code invariant shape
    exec store platform valid sourceWf ambient ambientWf address function identity signature args results owner functionAt host signatureAt owned accepted
    (fun p arguments defaults=>WP.spec_mono (callback p arguments defaults) (by
      rintro answer ⟨afterCode,agrees,fresh,extension,typed,matching⟩
      exact ⟨afterCode,agrees,fresh,extension,typed⟩)) preserve externs issued
  rw [graph,WP.spec_ok] at bounded
  rw [actual,WP.spec_ok]
  refine ⟨afterCode,fresh,typedStore _ _ fresh,kept,agrees,extension,?_⟩
  cases status : out.1 with
  | Ok unit =>
    obtain ⟨typed,sourceOwned,source,rawOwned⟩ := success status
    obtain ⟨sameEvents,sameTarget⟩ := Spec.chosen_terminal_unique admissible run terminal _ _ source (.values _ _)
    exact ⟨by simpa only [sameEvents] using graph,by simpa only [status] using And.intro sameTarget rawOwned⟩
  | Err error =>
    obtain ⟨otherCode,retained,returned,failed⟩ := bounded
    have cause := (failed error status).2
    have boundaryFalse := cause.excludes_boundary signatureFits available continuing overflow
    have meaning := failure error status
    cases error with
    | Trap trap =>
      obtain ⟨count,source⟩ := meaning
      obtain ⟨sameEvents,sameTarget⟩ := Spec.chosen_terminal_unique admissible run terminal _ _ source.erase_count (.trap _)
      exact ⟨by simpa only [sameEvents] using graph,by simpa only [status] using sameTarget⟩
    | Terminated => exact False.elim (boundaryFalse (Or.inl rfl))
    | Exhausted resource =>
      cases resource with
      | CallStack => exact False.elim (boundaryFalse (Or.inr (Or.inl rfl)))
      | Values => exact False.elim (boundaryFalse (Or.inr (Or.inr (Or.inl rfl))))
      | Allocation => exact False.elim (boundaryFalse (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      | Objects => exact False.elim (boundaryFalse (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | _ => exact False.elim meaning
end Exec.Theorems
