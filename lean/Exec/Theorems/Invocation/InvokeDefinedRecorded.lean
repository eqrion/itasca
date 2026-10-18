import Exec.Theorems.Api.RecordedInvTotal
import Exec.Theorems.Composition.Recorded.RecordedLoopSource
import Exec.Theorems.Composition.Supported.SupportedEntryOutcomes
import Exec.Interp.Invocation.InvokeRecordedPrefix
import Exec.Theorems.Api.ReadbackIssued
import Exec.Spec.HostCall
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- A defined public invocation has exactly the concrete recorder's labels in
its source result or error. Erasure recovers the extracted invocation. -/
theorem invoke_defined_recorded_outcomes
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
    (Inv : runtime.store.Store M → Prop)
    (certify : ∀s,Inv s → CertifiedSupportedStore emission allowed view code s)
    (update : ∀before after,Inv before → CumulativeStoreMutation view code before after → Inv after)
    (sound : Platform.HostSound hooks Inv (Store.decodeStore view code))
    (preserve : ∀ store, Inv store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀ store, Inv store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀ store, Inv store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer →
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.Function)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ())) :
    recordedInvokeWith memory hooks floats allocator exec store platform address args results []
      ⦃ (out,events) =>
        (Inv out.2.2.1 ∧ FrameStorePrefix store out.2.2.1 ∧
          Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1)) ∧
        (out.1=.Ok () →
          ResultsTyped (Store.decodeStore view code out.2.2.1) (signature.results.val.map sourceType)
            (out.2.2.2.2.val.map sourceValue) ∧
          Abs.Ownership.ValuesOwned (Store.ownershipBounds out.2.2.1) (out.2.2.2.2.val.map sourceValue) ∧
          (StepsH ⟨⟨Store.decodeStore view code store,ambient⟩,
            vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ events
            ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,vals (out.2.2.2.2.val.map sourceValue)⟩) ∧
          (∀value∈out.2.2.2.2.val,Store.ValueInStore out.2.2.1 value)) ∧
        (∀error,out.1=.Err error → EventfulInvocationError
          ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩
          events (Store.decodeStore view code out.2.2.1) ambient error) ⦄div := by
  have certified := certify store valid
  have storeWf := Store.decodeStore_wf view code store certified.shape certified.storeSyntax
  have arguments := checked_arguments_typed memory view code store storeWf args signature.params accepted owned
  have initialWf := Spec.host_call_wf (fa:=address.index.val) storeWf ambientWf arguments
  let retained := fun after => Inv after ∧ FrameStorePrefix store after ∧
    Extend_store (Store.decodeStore view code store) (Store.decodeStore view code after)
  let property := fun after values events =>
    ResultsTyped (Store.decodeStore view code after) (signature.results.val.map sourceType) values ∧
    Abs.Ownership.ValuesOwned (Store.ownershipBounds after) values ∧
    StepsH ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ events
      ⟨⟨Store.decodeStore view code after,ambient⟩,vals values⟩
  let errors := fun after error events => EventfulInvocationError
    ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩
    events (Store.decodeStore view code after) ambient error
  let entry := fun (after : runtime.store.Store M) (prepared : runtime.interp.Execution) (events : List HostEvent) => events=[] ∧ after=store ∧ ∃source,
    StructuredMachine.Execution emission (Abs.SupportedState allowed) view code store prepared source
      (signature.results.val.map sourceType) 0 false ∧
    Abs.Ownership.StatefulOwned (Store.ownershipBounds store) source ∧ source.ambient=ambient ∧
    StepH ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ [] (Abs.decode source)
  refine WP.dspec_mono (recorded_invoke_with_prefix_owned_causes_composition_mode memory hooks floats allocator true allocation exec store platform
    address function signature args results [] owner hf hs accepted (fun value member=>(owned value member).1)
    entry retained ⟨valid,.refl _,Spec.extend_store_refl _ storeWf⟩ property errors ?_ ?_ ?_ ?_) ?_
  · intro error cause
    cases error <;> try simp only [InvocationResourceCause] at cause
    rename_i limit
    exact ⟨_,StepsH.refl initialWf⟩
  · intro after values events kept satisfied refused
    obtain ⟨typed,ownership,reductions⟩ := satisfied
    exact ⟨vals values,reductions⟩
  · intro prepared p identity empty represented
    unfold recordedCall Platform.Recording.run
    apply WP.spec_bind (call_defined_supported_entry_outcomes memory hooks floats allocator allocation interrupts view code
      prepared store p certified.shape certified.storeSyntax certified.segmentBounds certified.typed certified.supported certified.compiled
      ambient ambientWf address function signature instanceIndex functionIndex args empty identity represented accepted owned hf hs hw)
    intro out outcome
    rw [callHostEvents_wasm hf hw]
    simp only [List.nil_append,WP.spec_ok]
    refine ⟨?_,?_,?_⟩
    · simpa only [outcome.1] using (show retained store from ⟨valid,.refl _,Spec.extend_store_refl _ storeWf⟩)
    · intro success
      exact ⟨rfl,outcome.1,outcome.2.1 success⟩
    · intro error failed
      obtain ⟨inst,compiled,hi,hc,cause⟩ := outcome.2.2 error failed
      change EventfulInvocationError _ [] _ _ _
      rw [outcome.1]
      rcases cause.kind with rfl | rfl | rfl | rfl <;> exact ⟨_,StepsH.refl initialWf⟩
  · intro after prepared p entryTrace entered
    obtain ⟨rfl,same,source,invariant,ownedSource,ambientEq,sourceStep⟩ := entered
    subst after
    let machine : EventfulMachine emission allowed M P view code (signature.results.val.map sourceType) :=
      ⟨store,prepared,p,source,0,false,invariant,certified,ownedSource⟩
    apply WP.dspec_mono (recorded_inv_loop_source_results memory hooks floats allocator Inv
      (recorded_inv_step_outcomes language memory hooks floats allocator correct allocation interrupts view laws code Inv certify update sound preserve externs issued _) machine valid)
    rintro ⟨out,events⟩ outcome
    obtain ⟨newValid,fresh,kept,extension,success,failed⟩ := outcome
    refine ⟨kept,⟨newValid,kept,extension⟩,?_,?_⟩
    · intro status
      obtain ⟨values,typed,ownedValues,represented,reductions⟩ := success status
      have tags : signature.results.val.map sourceType=values.map Code.valueType := by
        simpa only [show Code.valueType=Abs.valueType from funext valueType_eq_abs] using (Abs.results_type_of_typed typed).symm
      refine ⟨values,tags,Spec.resultsTyped_wf typed,?_,represented,typed,ownedValues,?_⟩
      · intro value member
        exact Store.owned_result_fits _ value (ownedValues value member)
      · simpa only [machine,ambientEq,List.nil_append] using StepsH.cons sourceStep reductions
    · intro error status
      have errorSource := failed error status
      have first : StepsH _ [] (Abs.decode source) := StepsH.cons sourceStep (StepsH.refl invariant.typed.typed.decode_wf)
      simpa only [machine,ambientEq,List.nil_append] using errorSource.prepend first
  · rintro ⟨out,events⟩ outcome
    refine ⟨outcome.1,?_,outcome.2.2⟩
    intro success
    obtain ⟨⟨typed,sourceOwned,reductions⟩,rawOwned⟩ := outcome.2.1 success
    refine ⟨typed,sourceOwned,reductions,?_⟩
    intro value member
    apply owned_source_value_in_store out.2.2.1 value (rawOwned value member)
    exact sourceOwned _ (List.mem_map.mpr ⟨value,member,rfl⟩)
end Exec.Theorems
