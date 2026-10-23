import Exec.Theorems.Composition.Core.CoreInstantiationResult
import Exec.Theorems.Invocation.InvokeCumulative
import Exec.Theorems.Composition.Cumulative.CumulativeStorePredicate
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

theorem invoke_defined_cumulative_store_predicate {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedCumulativeStore view code store) (hostFree : CoreHostFree store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()))
    (predicate : runtime.store.Store M → Prop) (initialPredicate : predicate store)
    (preserved : ∀ before after, CumulativeStoreMutation view code before after → predicate before → predicate after) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => predicate out.2.2.1 ⦄div := by
  let initial : config := ⟨⟨Store.decodeStore view code store,ambient⟩,
    vals (args.val.map Interp.sourceValue) ++ [.CALL_ADDR address.index.val]⟩
  let entry (prepared : runtime.interp.Execution) : Prop := ∃ source,
    Interp.Cumulative.Execution view code store prepared source (signature.results.val.map Interp.sourceType) 0 false ∧
    Abs.Ownership.StatefulOwned (Store.ownershipBounds store) source ∧ source.ambient = ambient ∧
    StepH initial [] (Abs.decode source)
  refine WP.dspec_mono (Interp.invoke_with_mutable_error_composition memory hooks floats allocator allocation exec store platform
    address function signature args results owner hf hs accepted (fun value member => (owned value member).1) entry
    predicate initialPredicate
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
    apply WP.dspec_mono (checked_results_conjoin
      (cumulative_loop memory hooks floats allocator correct allocation interrupts view laws code machine)
      (cumulative_loop_store_predicate memory hooks floats allocator correct allocation interrupts view laws code
        machine predicate initialPredicate preserved))
    rintro out ⟨outcome,retained⟩
    obtain ⟨fresh,metadata,extension,readback⟩ := outcome.readback
    refine ⟨metadata.identity,metadata.functions,metadata.types,retained,?_,by intros; trivial⟩
    intro success
    obtain ⟨values,tags,wf,fits,represented,steps⟩ := readback success
    exact ⟨values,tags,wf,fits,represented,trivial⟩

end Exec.Theorems
