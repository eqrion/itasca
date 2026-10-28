import Exec.Store.Initialization.ElementShapeLoop
import Exec.Store.Initialization.InitializerSourceContext
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
    (compiled : Code.InitializerCode code expr ty)
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
