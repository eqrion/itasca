import Itasca.Runtime.Store.Initialization.ElementShapeLoop
import Itasca.Runtime.Store.Initialization.InitializerSourceContext
import Itasca.Runtime.Representation.Collection

/-!
Source values of allocated element segments. Constant evaluation and encoded pushes establish the source-element initializer loop relation.
-/

/-! ## Element Source Values -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def ElementSourceValues (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (ty : Itasca.types.ElemType) (expressions : List Itasca.types.ConstExpr) (words : List U64) : Prop :=
  List.Forall₂ (fun expr word => Eval_expr ⟨sourceStore, ⟨[], sourceInstance⟩⟩
    (Itasca.ModuleConstants.expression expr) ⟨sourceStore, ⟨[], sourceInstance⟩⟩
    [refVal (decodeRef ty word)]) expressions words

theorem eval_const_source {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (expr : Itasca.types.ConstExpr) (ty : Itasca.types.ValueType) (words : List U64)
    (found : store.instances.val[instIndex.val]? = some inst)
    (codeFound : inst.module.functions.val[function.val]? = some code)
    (compiled : Compiler.InitializerCode code expr ty)
    (resolved : Interp.InitializerResolution store inst expr ty words)
    (bindings : InitializerBindings store inst)
    (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (storeWf : wf_store sourceStore) (frameWf : wf_frame ⟨[], sourceInstance⟩)
    (context : InitializerSourceContext sourceStore sourceInstance store inst)
    (valid : Itasca.ModuleConstants.Valid inst.module.module.env expr ty) :
    runtime.interp.eval_const memory hooks floats allocator store platform instIndex function ty
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧ ∀ value, out.1 = .Ok value →
        ValueInStore store value ∧ Interp.rawType value = ty ∧
        Eval_expr ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (Itasca.ModuleConstants.expression expr)
          ⟨sourceStore, ⟨[], sourceInstance⟩⟩ [Interp.sourceValue value] ⦄ := by
  have exactValue := eval_const_effect memory hooks floats allocator law store platform instIndex function
    inst code expr ty words found codeFound compiled resolved (initializer_reference_bound resolved bindings)
  obtain ⟨result, run, owned⟩ := WP.spec_imp_exists
    (eval_const_owned memory hooks floats allocator law store platform instIndex function
      inst code expr ty words found codeFound compiled resolved bindings)
  rw [run] at exactValue ⊢
  simp only [WP.spec_ok] at exactValue ⊢
  refine ⟨owned.1, owned.2.1, ?_⟩
  intro value success
  refine ⟨(owned.2.2 value success).1, (owned.2.2 value success).2, ?_⟩
  rw [(exactValue.2.2 value success).2]
  exact context.expression valid resolved storeWf frameWf

theorem encode_push_source {M : Type} (store : runtime.store.Store M)
    (values : alloc.vec.Vec U64) (value : runtime.Value) (ty : Itasca.types.ElemType)
    (typed : elementValueType ty = Interp.rawType value) (owned : ValueInStore store value)
    (previous : ∀ word ∈ values.val, ReferenceShape store ty word)
    (room : values.length < Usize.max)
    (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (expressions : List Itasca.types.ConstExpr) (expr : Itasca.types.ConstExpr)
    (matched : ElementSourceValues sourceStore sourceInstance ty expressions values.val)
    (evaluated : Eval_expr ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (Itasca.ModuleConstants.expression expr)
      ⟨sourceStore, ⟨[], sourceInstance⟩⟩ [Interp.sourceValue value]) :
    (do let (lo, _) ← runtime.value.encode value
        let next ← alloc.vec.Vec.push values lo
        .ok (next, (core.result.Result.Ok () : core.result.Result Unit runtime.ExecError)))
      ⦃ out => out.1.length = values.length + 1 ∧ out.2 = .Ok () ∧
        (∀ word ∈ out.1.val, ReferenceShape store ty word) ∧
        ElementSourceValues sourceStore sourceInstance ty (expressions ++ [expr]) out.1.val ⦄ := by
  obtain ⟨pair, encoded, canonical⟩ := WP.spec_imp_exists (encode_reference_shape store value ty typed owned)
  rw [encoded, bind_ok]
  rcases pair with ⟨lo, hi⟩
  have decoded := decode_encoded_value store value owned (lo, hi) encoded
  rw [← typed] at decoded
  have exactRef : refVal (decodeRef ty lo) = Interp.sourceValue value := by
    cases ty <;> simpa only [elementValueType, decodeWords] using decoded
  step as ⟨next, stored⟩
  refine ⟨by simp [stored], ?_, ?_⟩
  · intro word member
    simp only [stored, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact previous word old
    · exact canonical
  · unfold ElementSourceValues at matched ⊢
    rw [stored]
    exact List.rel_append matched (.cons (by simpa only [exactRef] using evaluated) .nil)
end Itasca.Runtime.Store

end

/-! ## Element Source Loop -/

section

namespace Itasca.Runtime.Store
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
        simp only [runtime.compiler.ExecutableModule.env,
          Itasca.module.Module.impl.env, Itasca.module.Env.impl.elements, bind_ok]
        step with Itasca.Runtime.Representation.slice_index_given inst.module.module.env.elements.deref index segment
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

end Itasca.Runtime.Store

end
