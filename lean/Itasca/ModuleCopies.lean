import Itasca.EnvTranslation

open Aeneas Aeneas.Std

namespace Itasca

/-- The allocation loop copies the remaining source in its original order. -/
@[step]
theorem module.copy_value_types_loop.spec (src : Slice types.ValueType)
    (out : alloc.vec.Vec types.ValueType) (i : Usize)
    (hi : i.val ≤ src.val.length)
    (hsize : out.val.length + (src.val.length - i.val) ≤ Usize.max) :
    module.copy_value_types_loop src out i ⦃ copied =>
      copied.val = out.val ++ src.val.drop i.val ⦄ := by
  unfold module.copy_value_types_loop
  apply loop.spec_decr_nat (fun p => src.val.length - p.2.val)
    (fun p => p.2.val ≤ src.val.length ∧
      p.1.val ++ src.val.drop p.2.val = out.val ++ src.val.drop i.val ∧
      p.1.val.length + (src.val.length - p.2.val) ≤ Usize.max)
  · rintro ⟨v, j⟩ ⟨hj, hv, hb⟩
    dsimp only at hj hv hb
    unfold module.copy_value_types_loop.body
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

@[step]
theorem module.copy_value_types.spec (src : Slice types.ValueType) :
    module.copy_value_types src ⦃ copied => copied.val = src.val ⦄ := by
  simpa [module.copy_value_types] using
    module.copy_value_types_loop.spec src (alloc.vec.Vec.new _) 0#usize
      (by simp) (by simp)

@[step]
theorem module.copy_func_type.spec (ft : types.FuncType) :
    module.copy_func_type ft ⦃ copied => copied = ft ⦄ := by
  unfold module.copy_func_type
  obtain ⟨p, hp, hpval⟩ := WP.spec_imp_exists
    (module.copy_value_types.spec (alloc.vec.Vec.deref ft.params))
  obtain ⟨r, hr, hrval⟩ := WP.spec_imp_exists
    (module.copy_value_types.spec (alloc.vec.Vec.deref ft.results))
  have hp' : p = ft.params := alloc.vec.Vec.ext _ _ (by simpa [alloc.vec.Vec.deref] using hpval)
  have hr' : r = ft.results := alloc.vec.Vec.ext _ _ (by simpa [alloc.vec.Vec.deref] using hrval)
  simp [hp, hr, hp', hr']

@[step]
theorem module.lookup_type.spec (env : module.Env) (idx : U32) :
    module.lookup_type env idx ⦃ r =>
      match r with
      | .Ok ft => ∃ hi : idx.val < env.types.val.length, env.types.val[idx.val] = ft
      | .Err e => e = .UnknownType idx ∧ env.types.val.length ≤ idx.val ⦄ := by
  unfold module.lookup_type
  step*

end Itasca
