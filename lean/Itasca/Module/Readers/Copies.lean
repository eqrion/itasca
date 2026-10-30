import Itasca.Support.EnvTranslation

/-!
# Copying and looking up types

Specs for the allocation helpers `metadata.copy_value_types`, `metadata.copy_func_type` (each returns
a copy equal to its source) and `metadata.lookup_type` (the indexed type, or `UnknownType` when the
index is out of range).
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- The copy loop appends the remaining source elements to `out` in order. -/
@[step]
theorem metadata.copy_value_types_loop.spec (src : Slice wasm_types.ValueType)
    (out : alloc.vec.Vec wasm_types.ValueType) (i : Usize)
    (hi : i.val ≤ src.val.length)
    (hsize : out.val.length + (src.val.length - i.val) ≤ Usize.max) :
    metadata.copy_value_types_loop src out i ⦃ copied =>
      copied.val = out.val ++ src.val.drop i.val ⦄ := by
  unfold metadata.copy_value_types_loop
  apply loop.spec_decr_nat (fun p => src.val.length - p.2.val)
    (fun p => p.2.val ≤ src.val.length ∧
      p.1.val ++ src.val.drop p.2.val = out.val ++ src.val.drop i.val ∧
      p.1.val.length + (src.val.length - p.2.val) ≤ Usize.max)
  · rintro ⟨v, j⟩ ⟨hj, hv, hb⟩
    dsimp only at hj hv hb
    unfold metadata.copy_value_types_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : j.val = src.val.length := by scalar_tac
      simp [heq] at hv
      simp [hv]
    · rename_i hmore
      have hlt : j.val < src.val.length := by scalar_tac
      have hcapacity : v.val.length < Usize.max := by omega
      step
      step
      step
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals try scalar_tac
      rw [out1_post, i2_post, vt_post, ← hv]
      simp only [List.append_assoc, List.singleton_append]
      rw [List.drop_eq_getElem_cons hlt]
  · exact ⟨hi, rfl, hsize⟩

/-- `metadata.copy_value_types` returns a vector equal to its source. -/
@[step]
theorem metadata.copy_value_types.spec (src : Slice wasm_types.ValueType) :
    metadata.copy_value_types src ⦃ copied => copied.val = src.val ⦄ := by
  simpa [metadata.copy_value_types] using
    metadata.copy_value_types_loop.spec src (alloc.vec.Vec.new _) 0#usize
      (by simp) (by simp)

/-- `metadata.copy_func_type` returns a function type equal to its source. -/
@[step]
theorem metadata.copy_func_type.spec (ft : wasm_types.FuncType) :
    metadata.copy_func_type ft ⦃ copied => copied = ft ⦄ := by
  unfold metadata.copy_func_type
  obtain ⟨p, hp, hpval⟩ := WP.spec_imp_exists
    (metadata.copy_value_types.spec (alloc.vec.Vec.deref ft.params))
  obtain ⟨r, hr, hrval⟩ := WP.spec_imp_exists
    (metadata.copy_value_types.spec (alloc.vec.Vec.deref ft.results))
  have hp' : p = ft.params := alloc.vec.Vec.ext _ _ (by simpa [alloc.vec.Vec.deref] using hpval)
  have hr' : r = ft.results := alloc.vec.Vec.ext _ _ (by simpa [alloc.vec.Vec.deref] using hrval)
  simp [hp, hr, hp', hr']

/-- `metadata.lookup_type` returns the type at the index, or `UnknownType` exactly when the index is
out of range. -/
@[step]
theorem metadata.lookup_type.spec (env : metadata.Env) (idx : U32) :
    metadata.lookup_type env idx ⦃ r =>
      match r with
      | .Ok ft => ∃ hi : idx.val < env.types.val.length, env.types.val[idx.val] = ft
      | .Err e => e = .UnknownType idx ∧ env.types.val.length ≤ idx.val ⦄ := by
  unfold metadata.lookup_type
  step*

end Itasca
