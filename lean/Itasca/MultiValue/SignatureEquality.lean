import Itasca.MultiValue.Typing

open Aeneas Aeneas.Std

namespace Itasca

/-- The comparison loop decides equality of the resolved lists, without
assuming descriptor identity (distinct type indices may have equal types). -/
theorem code.same_types_loop.spec (env : module.Env)
    (a b : signature.ResultType) (ts us : List types.ValueType)
    (ha : MultiValue.resolve env a = some ts)
    (hb : MultiValue.resolve env b = some us)
    (n i : Usize) (hn : n.val = ts.length) (hu : us.length = ts.length)
    (hi : i.val ≤ n.val) (hpre : ∀ j < i.val, ts[j]? = us[j]?) :
    code.same_types_loop env a b n i ⦃ r =>
      ∃ equal, r = .Ok equal ∧ (equal = true ↔ ts = us) ⦄ := by
  unfold code.same_types_loop
  apply loop.spec_decr_nat (fun j => n.val - j.val)
    (fun j => j.val ≤ n.val ∧ ∀ k < j.val, ts[k]? = us[k]?)
  · intro j ⟨hj, hp⟩
    unfold code.same_types_loop.body
    split
    · rename_i hend
      simp only [WP.spec_ok]
      refine ⟨true, rfl, ?_⟩
      simp only [true_iff]
      apply List.ext_getElem?
      intro k
      by_cases hk : k < j.val
      · exact hp k hk
      · rw [List.getElem?_eq_none (by scalar_tac), List.getElem?_eq_none (by scalar_tac)]
    · rename_i hlt
      have ht : j.val < ts.length := by scalar_tac
      have hus : j.val < us.length := by omega
      rw [signature.ResultType.get.complete a env ts ha j]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      rw [signature.ResultType.get.complete b env us hb j]
      simp only [bind_ok,
        List.getElem?_eq_getElem ht, List.getElem?_eq_getElem hus]
      step with core.cmp.PartialEq.ne.trait_default.spec
        types.ValueType.Insts.CoreCmpPartialEqValueType _ _ (types.ValueType.eq_spec _ _)
        as ⟨different, hdifferent⟩
      split
      · rename_i hne
        simp only [WP.spec_ok]
        refine ⟨false, rfl, ?_⟩
        simp only [Bool.false_eq_true, false_iff]
        intro he
        subst us
        simp_all
      · rename_i heq
        step
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro k hk
        by_cases hk' : k < j.val
        · exact hp k hk'
        · have hk' : k = j.val := by scalar_tac
          subst k
          simp_all
  · exact ⟨hi, hpre⟩

/-- Totality and exact equality for arbitrary descriptor pairs. -/
@[step]
theorem code.same_types.spec (env : module.Env) (a b : signature.ResultType) :
    code.same_types env a b ⦃ r =>
      match r with
      | .Ok equal => ∃ ts us, MultiValue.resolve env a = some ts ∧
          MultiValue.resolve env b = some us ∧ (equal = true ↔ ts = us)
      | .Err e => e = .UnknownType ∧
          (MultiValue.resolve env a = none ∨ MultiValue.resolve env b = none) ⦄ := by
  obtain ⟨ra, hra, hsa⟩ := WP.spec_imp_exists (signature.ResultType.len.spec a env)
  unfold code.same_types
  rw [hra]
  cases ra with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hsa.1, hsa.2]
  | Ok n =>
    obtain ⟨ts, ha, hn⟩ := hsa
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨rb, hrb, hsb⟩ := WP.spec_imp_exists (signature.ResultType.len.spec b env)
    rw [hrb]
    cases rb with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hsb.1, hsb.2]
    | Ok m =>
      obtain ⟨us, hb, hm⟩ := hsb
      simp only [bind_ok]
      split
      · rename_i hne
        simp only [WP.spec_ok]
        refine ⟨ts, us, ha, hb, ?_⟩
        simp only [Bool.false_eq_true, false_iff]
        intro he
        have : n = m := by scalar_tac
        simp_all
      · rename_i he
        apply WP.spec_mono (code.same_types_loop.spec env a b ts us ha hb
          n 0#usize hn (by scalar_tac) (by scalar_tac) (by simp))
        rintro r ⟨equal, rfl, hs⟩
        exact ⟨ts, us, ha, hb, hs⟩

theorem code.same_types.complete (env : module.Env) (a b : signature.ResultType)
    (ts : List types.ValueType) (ha : MultiValue.resolve env a = some ts)
    (hb : MultiValue.resolve env b = some ts) :
    code.same_types env a b = .ok (.Ok true) := by
  obtain ⟨r, hr, hs⟩ := WP.spec_imp_exists (code.same_types.spec env a b)
  cases r with
  | Err e => simp [ha, hb] at hs
  | Ok equal =>
    obtain ⟨ts', us', ha', hb', he⟩ := hs
    have ht : ts' = ts := by simpa [ha] using ha'.symm
    have hu : us' = ts := by simpa [hb] using hb'.symm
    have heq : equal = true := he.mpr (ht.trans hu.symm)
    simpa [heq] using hr

end Itasca
