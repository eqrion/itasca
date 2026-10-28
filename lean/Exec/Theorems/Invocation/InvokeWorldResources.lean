import Exec.Theorems.Composition.Eventful.EventfulWorldTotal
import Exec.Theorems.Composition.World.WorldLoopResources
import Exec.Theorems.Api.InvocationEntryResources
import Exec.Theorems.Composition.Supported.SupportedEntryOutcomes
import Exec.Interp.Invocation.InvokeRecordedPrefix
import Exec.Theorems.Api.ReadbackIssued
import Exec.Spec.HostCall
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

/-- A public failure is explained at its original signature/entry boundary or
at an actual source-reachable dispatch in the then-current code world. -/
def WorldDefinedSourceResourceCause {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (store : runtime.store.Store M) (ambient : frame) (address : runtime.FuncAddr)
    (signature : Itasca.types.FuncType) (args : Slice runtime.Value)
    (after : runtime.store.Store M) (error : runtime.ExecError) : Prop :=
  let initial := ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩
  CanonicalInvocationResourceCause allocator hooks initial (Store.decodeStore view code store)
    (Store.decodeFuncType signature) address.index.val store.limits.max_values.val store.limits.max_frames.val error ∨
  ∃ first : EventfulWorld M P view (signature.results.val.map sourceType),
    first.code=code ∧ first.machine.store=store ∧ StepH initial [] (Abs.decode first.machine.source) ∧
    ∃ result,result.2.2.2.2.2.1=after ∧ WorldLoopResourceCause memory hooks floats allocator Inv first result error

/-- Actual public defined-function invocation keeps one selected final code
world with its invariant, source outcomes and issued readback values. -/
theorem invoke_defined_world_recorded_resources
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Store.CodeInterpretation)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀ c s,Inv c s → CertifiedSupportedStore view c s)
    (update : ∀ c before after,Inv c before → CumulativeStoreMutation view c before after → Inv c after)
    (capacities : ∀ c s,Inv c s → Store.FunctionCapacities c s)
    (callbacks : HostLaws hooks view Inv)
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
    recordedInvokeWith memory hooks floats allocator exec store platform address args results []
      ⦃ (out,events) => ∃ afterCode,
        Inv afterCode out.2.2.1 ∧ FrameStorePrefix store out.2.2.1 ∧ Store.CodeAgreesOn store code afterCode ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode out.2.2.1) ∧
        (out.1=.Ok () →
          ResultsTyped (Store.decodeStore view afterCode out.2.2.1) (signature.results.val.map sourceType)
            (out.2.2.2.2.val.map sourceValue) ∧
          Abs.Ownership.ValuesOwned (Store.ownershipBounds out.2.2.1) (out.2.2.2.2.val.map sourceValue) ∧
          (StepsH ⟨⟨Store.decodeStore view code store,ambient⟩,
            vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ events
            ⟨⟨Store.decodeStore view afterCode out.2.2.1,ambient⟩,vals (out.2.2.2.2.val.map sourceValue)⟩) ∧
          (∀value∈out.2.2.2.2.val,Store.ValueInStore out.2.2.1 value)) ∧
        (∀error,out.1=.Err error → EventfulInvocationError
          ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩
          events (Store.decodeStore view afterCode out.2.2.1) ambient error ∧
          WorldDefinedSourceResourceCause memory hooks floats allocator view code Inv
            store ambient address signature args out.2.2.1 error) ⦄div := by
  have certified := certify code store valid
  have storeWf := Store.decodeStore_wf view code store certified.shape certified.storeSyntax
  have arguments := checked_arguments_typed memory view code store storeWf args signature.params accepted owned
  have initialWf := Spec.host_call_wf (fa:=address.index.val) storeWf ambientWf arguments
  let retained := fun after => FrameStorePrefix store after
  let property := fun after values events => ∃ afterCode,
    Inv afterCode after ∧ Store.CodeAgreesOn store code afterCode ∧
    Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode after) ∧
    ResultsTyped (Store.decodeStore view afterCode after) (signature.results.val.map sourceType) values ∧
    Abs.Ownership.ValuesOwned (Store.ownershipBounds after) values ∧
    StepsH ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ events
      ⟨⟨Store.decodeStore view afterCode after,ambient⟩,vals values⟩
  let errors := fun after error events => ∃ afterCode,
    Inv afterCode after ∧ Store.CodeAgreesOn store code afterCode ∧
    Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode after) ∧
    EventfulInvocationError
      ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩
      events (Store.decodeStore view afterCode after) ambient error ∧
      WorldDefinedSourceResourceCause memory hooks floats allocator view code Inv
        store ambient address signature args after error
  let entry := fun (after : runtime.store.Store M) (prepared : runtime.interp.Execution) (events : List HostEvent) => events=[] ∧ after=store ∧ ∃source,
    StructuredMachine.Execution view code store prepared source
      (signature.results.val.map sourceType) 0 false ∧
    Abs.Ownership.StatefulOwned (Store.ownershipBounds store) source ∧ source.ambient=ambient ∧
    StepH ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ [] (Abs.decode source)
  refine (DivSpec.mono (recorded_invoke_with_prefix_owned_causes_composition_mode memory hooks floats allocator True laws.allocCorrect exec store platform
    address function signature args results [] owner hf hs accepted (fun value member=>(owned value member).1)
    entry retained (.refl _) property errors ?_ ?_ ?_ ?_) ?_).dspec
  · intro error cause
    refine ⟨code,valid,(by intro index inst found fn; rfl),Spec.extend_store_refl _ storeWf,?_,Or.inl (InvocationResourceCause.canonical _ _ _ cause)⟩
    cases error <;> try simp only [InvocationResourceCause] at cause
    rename_i limit
    exact ⟨_,StepsH.refl initialWf⟩
  · intro after values events kept satisfied refused
    obtain ⟨afterCode,fresh,agrees,extension,typed,ownership,reductions⟩ := satisfied
    refine ⟨afterCode,fresh,agrees,extension,⟨vals values,reductions⟩,Or.inl ?_⟩
    apply Or.inl; apply Or.inr
    obtain ⟨n,amount,refusal⟩ := refused
    exact ⟨results,n,by simpa only [Store.decodeFuncType,List.length_map] using Nat.le_trans (Nat.le_of_eq amount) (Nat.sub_le _ _),refusal⟩
  · intro prepared p identity empty represented
    unfold recordedCall Platform.Recording.run
    apply DivSpec.of_spec
    apply WP.spec_bind (call_defined_supported_entry_outcomes memory hooks floats allocator laws.allocCorrect laws.interruptsReturn view code
      prepared store p certified.shape certified.storeSyntax certified.segmentBounds certified.typed certified.supported certified.compiled
      ambient ambientWf address function signature instanceIndex functionIndex args empty identity represented accepted owned hf hs hw)
    intro out outcome
    rw [callHostEvents_wasm hf hw]
    simp only [List.nil_append,WP.spec_ok]
    refine ⟨?_,?_,?_⟩
    · simpa only [outcome.1] using (show retained store from .refl _)
    · intro success
      exact ⟨rfl,outcome.1,outcome.2.1 success⟩
    · intro error failed
      obtain ⟨inst,compiled,hi,hc,cause⟩ := outcome.2.2 error failed
      change errors out.2.2.1 error []
      rw [outcome.1]
      refine ⟨code,valid,(by intro index inst found fn; rfl),Spec.extend_store_refl _ storeWf,?_,Or.inl ?_⟩
      · rcases cause.kind with rfl | rfl | rfl | rfl <;> exact ⟨_,StepsH.refl initialWf⟩
      · exact CallCause.invocation_canonical view code _ (capacities code store valid) certified.typed address function
          instanceIndex functionIndex inst compiled hf hw hi hc empty cause
  · intro after prepared p entryTrace entered
    obtain ⟨rfl,same,source,invariant,ownedSource,ambientEq,sourceStep⟩ := entered
    subst after
    let machine : EventfulWorld M P view (signature.results.val.map sourceType) :=
      ⟨code,⟨store,prepared,p,source,0,false,invariant,certified,ownedSource⟩⟩
    refine DivSpec.of_dspec ?_ fun _ => trivial
    apply WP.dspec_mono (world_recorded_loop_resource_results memory hooks floats allocator Inv capacities
      (world_step_outcomes memory hooks floats allocator view laws Inv certify update callbacks _) machine valid)
    rintro ⟨out,events⟩ outcome
    obtain ⟨⟨afterCode,newValid,fresh,kept,agrees,extension,success,failed⟩,causes⟩ := outcome
    refine ⟨kept,kept,?_,?_⟩
    · intro status
      obtain ⟨values,typed,ownedValues,represented,reductions⟩ := success status
      have tags : signature.results.val.map sourceType=values.map Code.valueType := by
        simpa only [show Code.valueType=Abs.valueType from funext valueType_eq_abs] using (Abs.results_type_of_typed typed).symm
      refine ⟨values,tags,Spec.resultsTyped_wf typed,?_,represented,afterCode,newValid,agrees,extension,typed,ownedValues,?_⟩
      · intro value member
        exact Store.owned_result_fits _ value (ownedValues value member)
      · simpa only [machine,ambientEq,List.nil_append] using StepsH.cons sourceStep reductions
    · intro error status
      have errorSource := failed error status
      refine ⟨afterCode,newValid,agrees,extension,?_,Or.inr ⟨machine,rfl,rfl,sourceStep,out,rfl,causes error status⟩⟩
      have first : StepsH _ [] (Abs.decode source) := StepsH.cons sourceStep (StepsH.refl invariant.typed.typed.decode_wf)
      simpa only [machine,ambientEq,List.nil_append] using errorSource.prepend first
  · rintro ⟨out,events⟩ outcome
    cases status : out.1 with
    | Ok unit =>
      cases unit
      obtain ⟨⟨afterCode,fresh,agrees,extension,typed,sourceOwned,reductions⟩,rawOwned⟩ := outcome.2.1 status
      refine ⟨afterCode,fresh,outcome.1,agrees,extension,?_,?_⟩
      · intro _
        refine ⟨typed,sourceOwned,reductions,?_⟩
        intro value member
        apply owned_source_value_in_store out.2.2.1 value (rawOwned value member)
        exact sourceOwned _ (List.mem_map.mpr ⟨value,member,rfl⟩)
      · intro error failed
        simp only [status] at failed
        cases failed
    | Err error =>
      obtain ⟨afterCode,fresh,agrees,extension,reductions⟩ := outcome.2.2 error status
      refine ⟨afterCode,fresh,outcome.1,agrees,extension,?_,?_⟩
      · intro success
        simp only [status] at success
        cases success
      · intro reported failed
        have equal : error=reported := by simpa only [status,core.result.Result.Err.injEq] using failed
        subst reported
        exact reductions
end Itasca.Runtime.Theorems
