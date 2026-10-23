import Exec.Representation.Collection
import Exec.Store.Initialization.ElementSourceValues

namespace Exec.Store
open Aeneas Aeneas.Std

private theorem elem_value_type_eq (ty : Itasca.types.ElemType) :
    types.ElemType.value_type ty = .ok (elementValueType ty) := by cases ty <;> rfl

theorem element_initializers_source_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index length : Usize)
    (inst : runtime.store.ModuleInst) (segment : Itasca.module.Element)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (helem : inst.module.module.env.elements.val[index.val]? = some segment)
    (hlength : length.val = segment.init.length)
    (certificates : ElementInitializers store inst index segment)
    (bindings : InitializerBindings store inst)
    (values : alloc.vec.Vec U64) (j : Usize) (status : core.result.Result Unit runtime.ExecError)
    (hvalues : values.length ≤ j.val) (hj : j.val ≤ length.val)
    (shaped : ∀ word ∈ values.val, ReferenceShape store segment.elem word)
    (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (storeWf : wf_store sourceStore) (frameWf : wf_frame ⟨[], sourceInstance⟩)
    (context : InitializerSourceContext sourceStore sourceInstance store inst)
    (valid : ∀ expr ∈ segment.init.val,
      Itasca.ModuleConstants.Valid inst.module.module.env expr (elementValueType segment.elem))
    (matched : status = .Ok () → ElementSourceValues sourceStore sourceInstance segment.elem
      (segment.init.val.take j.val) values.val) :
    runtime.store.instantiate.Store.add_instance_element_loop memory hooks floats allocator store platform
      instIndex index length values j status ⦃ out =>
        out.1 = store ∧ out.2.1 = platform ∧ out.2.2.1.length ≤ length.val ∧
        (∀ word ∈ out.2.2.1.val, ReferenceShape store segment.elem word) ∧
        (out.2.2.2 = .Ok () → ElementSourceValues sourceStore sourceInstance segment.elem segment.init.val out.2.2.1.val) ⦄ := by
  have segmentLength : length.val = segment.init.val.length := hlength
  unfold runtime.store.instantiate.Store.add_instance_element_loop
  apply loop.spec_decr_nat (fun p => length.val - p.2.2.2.1.val)
    (fun p => p.1 = store ∧ p.2.1 = platform ∧
      p.2.2.1.length ≤ p.2.2.2.1.val ∧ p.2.2.2.1.val ≤ length.val ∧
      (∀ word ∈ p.2.2.1.val, ReferenceShape store segment.elem word) ∧
      (p.2.2.2.2 = .Ok () → ElementSourceValues sourceStore sourceInstance segment.elem
        (segment.init.val.take p.2.2.2.1.val) p.2.2.1.val))
  · rintro ⟨current, host, vals, k, state⟩ ⟨hcurrent, hhost, hvals, hk, refs, currentMatched⟩
    dsimp only at hcurrent hhost hvals hk refs currentMatched ⊢
    subst current host
    change vals.val.length ≤ k.val at hvals
    unfold runtime.store.instantiate.Store.add_instance_element_loop.body
    split
    · rename_i more
      have hmore : k.val < length.val := by scalar_tac
      cases state with
      | Err error =>
        simp [core.result.Result.is_ok]
        exact ⟨by omega, refs⟩
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        obtain ⟨functions, mapping, certificates⟩ := certificates
        obtain ⟨expr, function, code, words, hexpr, hfunction, hcode, compiled, resolved⟩ :=
          certificates k (by omega)
        step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
        subst found
        step with Interp.vec_index_given inst.module.element_initializers index functions mapping
          as ⟨found, hfound⟩
        subst found
        step with Interp.vec_index_given functions k function hfunction as ⟨found, hfound⟩
        subst found
        simp only [runtime.compiler.ExecutableModule.env, module.Module.env,
          Itasca.module.Module.impl.env, module.Env.elements, Itasca.module.Env.impl.elements, bind_ok]
        step with Exec.Representation.slice_index_given inst.module.module.env.elements.deref index segment
          (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
        subst found
        rw [elem_value_type_eq, bind_ok]
        step with eval_const_source memory hooks floats allocator law store platform instIndex function
          inst code expr (elementValueType segment.elem) words hi hcode compiled resolved bindings
          sourceStore sourceInstance storeWf frameWf context
          (valid expr (List.mem_of_getElem? hexpr))
          as ⟨result, after, host', hs, hp, hvalue⟩
        subst after host'
        cases result with
        | Err error =>
          step as ⟨next, hnext⟩
          change vals.val.length ≤ next.val ∧ next.val ≤ length.val ∧
            (∀ word ∈ vals.val, ReferenceShape store segment.elem word) ∧
            ((core.result.Result.Err error : core.result.Result Unit runtime.ExecError) = .Ok () → _ ) ∧
            length.val - next.val < length.val - k.val
          exact ⟨by omega, by omega, refs, by simp, by omega⟩
        | Ok value =>
          obtain ⟨owned, typed, evaluated⟩ := hvalue value rfl
          have room : vals.length < Usize.max := by scalar_tac
          apply WP.spec_bind (encode_push_source store vals value segment.elem typed.symm owned refs room
            sourceStore sourceInstance (segment.init.val.take k.val) expr (currentMatched rfl) evaluated)
          rintro ⟨pushed, nextStatus⟩ ⟨hpush, hstatus, pushedRefs, pushedMatched⟩
          step as ⟨next, hnext⟩
          refine ⟨?_, by omega, pushedRefs, ?_, by omega⟩
          · rw [hpush]
            change vals.val.length + 1 ≤ next.val
            omega
          · intro _
            rw [hnext, List.take_succ_eq_append_getElem (by omega)]
            have exprEq := (List.getElem?_eq_some_iff.mp hexpr).2
            simpa only [exprEq] using pushedMatched
    · have hstop : length.val ≤ k.val := by scalar_tac
      simp only [WP.spec_ok]
      simp only [true_and]
      change vals.val.length ≤ length.val ∧ (∀ word ∈ vals.val, ReferenceShape store segment.elem word) ∧
        (state = .Ok () → ElementSourceValues sourceStore sourceInstance segment.elem segment.init.val vals.val)
      refine ⟨by omega, refs, ?_⟩
      intro success
      have atEnd : k.val = segment.init.val.length := by omega
      simpa only [atEnd, List.take_length] using currentMatched success
  · exact ⟨rfl, rfl, hvalues, hj, shaped, matched⟩

end Exec.Store
