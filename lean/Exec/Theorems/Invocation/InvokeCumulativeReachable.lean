import Exec.Theorems.Invocation.InvokeCumulative
import Exec.Theorems.Composition.Cumulative.CumulativeReachable
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

theorem invoke_defined_cumulative_reachable {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedCumulativeStore view code store) (hostFree : CoreHostFree store)
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
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => StoreReachable
        ⟨⟨Store.decodeStore view code store,ambient⟩,
          vals (args.val.map Interp.sourceValue) ++ [.CALL_ADDR address.index.val]⟩
        (Store.decodeStore view code out.2.2.1) ⦄div := by
  let initial : config := ⟨⟨Store.decodeStore view code store,ambient⟩,
    vals (args.val.map Interp.sourceValue) ++ [.CALL_ADDR address.index.val]⟩
  let entry (prepared : runtime.interp.Execution) : Prop := ∃ source,
    Interp.Cumulative.Execution view code store prepared source (signature.results.val.map Interp.sourceType) 0 false ∧
    Abs.Ownership.StatefulOwned (Store.ownershipBounds store) source ∧ source.ambient = ambient ∧
    StepH initial [] (Abs.decode source)
  have initialWf : wf_config initial := by
    apply wf_config.config_case_0
    · exact .state_case_0 _ _ (Store.decodeStore_wf view code store certified.shape certified.storeSyntax) ambientWf
    · apply Spec.forall_append
      · apply Spec.wf_vals
        intro value member
        obtain ⟨raw,member,rfl⟩ := List.mem_map.mp member
        exact Interp.sourceValue_wf raw
      · simp only [Forall,List.mem_singleton]
        intro instruction same
        subst instruction
        exact .admininstr_case_70 _
  have initialReachable : StoreReachable initial (Store.decodeStore view code store) :=
    ⟨ambient,_,StepsH.refl initialWf⟩
  refine WP.dspec_mono (Interp.invoke_with_mutable_error_composition memory hooks floats allocator allocation exec store platform
    address function signature args results owner hf hs accepted (fun value member => (owned value member).1) entry
    (fun after => StoreReachable initial (Store.decodeStore view code after)) initialReachable
    (fun _ _ => True) (fun _ _ => True) (by intros; trivial) ?_ ?_) (fun _ post => post.1)
  · intro prepared p identity empty arguments
    apply WP.spec_mono (call_defined_cumulative_entry_certified memory hooks floats allocator allocation interrupts view code
      prepared store p certified ambient ambientWf address function signature instanceIndex functionIndex
      args empty identity arguments accepted owned hf hs hw)
    intro out post
    exact ⟨post.1,post.2,by intros; trivial⟩
  · intro prepared p entered
    obtain ⟨source,invariant,ownedSource,ambientEq,sourceStep⟩ := entered
    let machine : CumulativeMachine M P view code (signature.results.val.map Interp.sourceType) :=
      ⟨store,prepared,p,source,0,false,invariant,certified,ownedSource,hostFree⟩
    apply WP.dspec_mono (cumulative_loop memory hooks floats allocator correct allocation interrupts view laws code machine)
    intro out outcome
    obtain ⟨fresh,metadata,extension,readback⟩ := outcome.readback
    refine ⟨metadata.identity,metadata.functions,metadata.types,outcome.reachable.prepend sourceStep,?_,by intros; trivial⟩
    intro success
    obtain ⟨values,tags,wf,fits,represented,steps⟩ := readback success
    exact ⟨values,tags,wf,fits,represented,trivial⟩

end Exec.Theorems
