import Itasca.Runtime.Interp.Invocation.PrefixCauses

/-!
Public-wrapper divergence must come from an entered interpreter loop; metadata prefixes permit host callbacks to publish new functions.

Main declarations: `invoke_prefix_divergent_entry`. A direct consumer is `Integration.Invocation.DefinedDivergence`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

private theorem total_of_nondivergent {α : Type} {run : Result α} {post : α → Prop}
    (safe : WP.dspec run post) (nondivergent : run ≠ .div) : WP.spec run post := by
  cases safe with
  | ret satisfied => exact .ret satisfied
  | div => exact False.elim (nondivergent rfl)

/-- Public-wrapper divergence must come from an entered interpreter loop;
metadata prefixes permit host callbacks to publish new functions. -/
theorem invoke_prefix_divergent_entry {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.types.FuncType) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store=store.id)
    (hf : store.funcs.val[address.index.val]?=some function)
    (hs : store.types.val[function.signature.val]?=some signature)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params)=.ok (.Ok ()))
    (owned : ∀value∈args.val,ValueOwnedFits store.id value)
    (entry : runtime.store.Store M → runtime.interp.Execution → Prop)
    (called : ∀prepared p,prepared.store=store.id → prepared.frames.val=[] →
      ValuesAt prepared.slots.val 0 (args.val.map sourceValue) →
      runtime.interp.call memory hooks floats allocator prepared store p address 0#usize ⦃ out =>
        out.1=.Ok () → entry out.2.2.1 out.2.1 ⦄)
    (executed : ∀after prepared p,entry after prepared →
      runtime.interp.invoke_with_loop1 memory hooks floats allocator prepared after p (.Ok ())
        ⦃ (_,words,_,_,_,afterStore,_,status) => FrameStorePrefix store afterStore ∧
          (status=.Ok () → ∃values,
            signature.results.val.map sourceType=values.map Compiler.valueType ∧
            (∀value∈values,wf_val value) ∧ (∀value∈values,ResultIndexFits value) ∧
            ValuesAt words.val 0 values) ⦄div)
    (diverges : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results=.div) :
    ∃after prepared p,entry after prepared ∧
      runtime.interp.invoke_with_loop1 memory hooks floats allocator prepared after p (.Ok ())=.div := by
  classical
  by_contra absent
  have total : WP.spec
      (runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results)
      (fun out=>True ∧ (out.1=.Ok () → True) ∧ (∀error,out.1=.Err error → True)) := by
    refine (invoke_with_prefix_causes_composition_mode memory hooks floats allocator False allocation exec store platform
      address function signature args results owner hf hs accepted owned entry (fun _=>True) trivial (fun _ _=>True)
      (fun _ _=>True) (by intros; trivial) ?_ ?_).spec
    · intro prepared p identity empty arguments
      apply DivSpec.of_spec
      apply WP.spec_mono (called prepared p identity empty arguments)
      intro out post
      exact ⟨trivial,post,by intros; trivial⟩
    · intro after prepared p entered
      have safe := executed after prepared p entered
      have normal : WP.spec
          (runtime.interp.invoke_with_loop1 memory hooks floats allocator prepared after p (.Ok ()))
          (fun (_,words,_,_,_,afterStore,_,status)=> FrameStorePrefix store afterStore ∧
            (status=.Ok () → ∃values,signature.results.val.map sourceType=values.map Compiler.valueType ∧
              (∀value∈values,wf_val value) ∧ (∀value∈values,ResultIndexFits value) ∧ ValuesAt words.val 0 values)) := by
        apply total_of_nondivergent safe
        intro divergent
        exact absent ⟨after,prepared,p,entered,divergent⟩
      apply DivSpec.of_spec
      apply WP.spec_mono normal
      rintro out ⟨metadata,success⟩
      refine ⟨metadata,trivial,?_,by intros; trivial⟩
      intro ok
      obtain ⟨values,tags,wf,fits,represented⟩ := success ok
      exact ⟨values,tags,wf,fits,represented,trivial⟩
  rw [diverges] at total
  exact WP.spec_div.mp total
end Itasca.Runtime.Interp
