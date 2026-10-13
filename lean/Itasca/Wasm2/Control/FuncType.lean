import Itasca.Wasm2.ResultStackSemantics
import Itasca.Handler.ResumePrefix

open Aeneas Aeneas.Std

namespace Itasca

theorem code.check_func_type.complete (ft : types.FuncType)
    (hp : ft.params.val.length ≤ 1000) (hr : ft.results.val.length ≤ 1000) :
    code.check_func_type ft = .ok (.Ok ()) := by
  have hp' : ¬ alloc.vec.Vec.len ft.params > limits.MAX_MULTI_VALUE_PARAMS := by
    simp only [limits.MAX_MULTI_VALUE_PARAMS]; scalar_tac
  have hr' : ¬ alloc.vec.Vec.len ft.results > limits.MAX_MULTI_VALUE_RESULTS := by
    simp only [limits.MAX_MULTI_VALUE_RESULTS]; scalar_tac
  simp [code.check_func_type, hp', hr']

/-- Multi-value calls are total on structurally bounded stacks. The explicit
capacity guard also covers arbitrary oversized caller-supplied environments. -/
@[step]
theorem code.apply_func_type.total (st : code.OpIterState) (ft : types.FuncType)
    (hshape : Control.Shape st) :
    code.apply_func_type st ft ⦃ r =>
      Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
        r.2.vals.val.length ≤ st.vals.val.length + 1000 ⦄ := by
  obtain ⟨check, hcheck, hlimit⟩ := WP.spec_imp_exists (code.check_func_type.spec ft)
  unfold code.apply_func_type
  rw [hcheck]
  cases check with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hshape]
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨⟨res, s⟩, hpop, hs, hc, hp, hl, _⟩ := WP.spec_imp_exists
      (code.pop_types.total st (alloc.vec.Vec.deref ft.params) hshape)
    dsimp only at hs hc hp hl
    rw [hpop]
    cases res with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hs, hc, hp]
      omega
    | Ok u =>
      simp only [bind_ok]
      step
      split
      · simp [hs, hc, hp]
        omega
      · have hcap : s.vals.val.length + (alloc.vec.Vec.deref ft.results).val.length ≤ Usize.max := by
          simp [alloc.vec.Vec.deref]
          scalar_tac
        obtain ⟨s', hpush, hv', hc', hp'⟩ := WP.spec_imp_exists
          (code.push_types.spec s (alloc.vec.Vec.deref ft.results) hcap)
        rw [hpush]
        simp only [bind_ok, WP.spec_ok]
        refine ⟨hs.replace_operands hc' ?_, hc'.trans hc, hp'.trans hp, ?_⟩
        · have hbase := hs.base_le
          simp only [hv', List.length_append, List.length_map]
          omega
        · have hresults : ft.results.val.length ≤ 1000 := hlimit.2
          simp only [hv', List.length_append, List.length_map]
          simp only [alloc.vec.Vec.deref]
          simp
          omega

/-- An accepted call consumes its parameters in operand order and appends all
results. The semantic transfer is independent of the function's arity. -/
theorem code.apply_func_type.realizes (st : code.OpIterState) (ft : types.FuncType)
    (outer segment : List code.StackType)
    (hv : st.vals.val = outer ++ segment) (hb : (Control.base st).val = outer.length) :
    code.apply_func_type st ft ⦃ r =>
      r.1 = .Ok () → r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ft.params.val.length ≤ 1000 ∧ ft.results.val.length ≤ 1000 ∧
      ∃ rest, r.2.vals.val = outer ++ (rest ++ ft.results.val.map code.StackType.Val) ∧
        rest.length ≤ segment.length ∧
        ∀ ts, Sequence.Realizes (Control.polymorphic st) rest ts →
          Sequence.Realizes (Control.polymorphic st) segment
            (ts ++ ft.params.val.map Translate.valueType) ⦄ := by
  obtain ⟨check, hcheck, hc⟩ := WP.spec_imp_exists (code.check_func_type.spec ft)
  unfold code.apply_func_type
  rw [hcheck]
  cases check with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨⟨res, s⟩, hr, hcs, hps, rest, hvs, hlen, ht⟩ := WP.spec_imp_exists
      (code.pop_types.realizes st outer segment (alloc.vec.Vec.deref ft.params) hv hb)
    rw [hr]
    cases res with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok u =>
      simp only [bind_ok]
      step
      split
      · simp
      · step with code.push_types.spec s (alloc.vec.Vec.deref ft.results) (by simp [alloc.vec.Vec.deref]; scalar_tac)
        simp_all [alloc.vec.Vec.deref, List.append_assoc]

/-- Declarative operand compatibility forces call acceptance within the
profile's signature limits and available stack capacity. -/
theorem code.apply_func_type.complete (st : code.OpIterState) (ft : types.FuncType)
    (outer segment : List code.StackType) (before : List valtype)
    (hp : ft.params.val.length ≤ 1000) (hr : ft.results.val.length ≤ 1000)
    (hv : st.vals.val = outer ++ segment) (hb : (Control.base st).val = outer.length)
    (hcap : st.vals.val.length + ft.results.val.length ≤ Usize.max)
    (ht : Sequence.Realizes (Control.polymorphic st) segment
      (before ++ ft.params.val.map Translate.valueType)) :
    code.apply_func_type st ft ⦃ r =>
      r.1 = .Ok () ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧
        rest.length ≤ segment.length + ft.results.val.length ∧
        Sequence.Realizes (Control.polymorphic st) rest
          (before ++ ft.results.val.map Translate.valueType) ⦄ := by
  obtain ⟨⟨_, s⟩, hpop, rfl, hc, hpos, rest, hvs, hlen, ht'⟩ := WP.spec_imp_exists
    (code.pop_types.complete st outer segment before (alloc.vec.Vec.deref ft.params)
      hv hb (by simpa [alloc.vec.Vec.deref] using ht))
  have hspace : s.vals.val.length + ft.results.val.length ≤ Usize.max := by
    simp only [hvs, hv, List.length_append] at *
    omega
  unfold code.apply_func_type
  rw [code.check_func_type.complete ft hp hr]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [hpop]
  simp only [bind_ok]
  step
  split
  · scalar_tac
  · step with code.push_types.spec s (alloc.vec.Vec.deref ft.results) (by simpa [alloc.vec.Vec.deref] using hspace)
    refine ⟨by simp_all, by simp_all,
      rest ++ ft.results.val.map code.StackType.Val, ?_, ?_, ?_⟩
    · simp_all [alloc.vec.Vec.deref, List.append_assoc]
    · simpa using Nat.add_le_add_right hlen ft.results.val.length
    · exact (Sequence.realizes_append_concrete _ rest ft.results.val _).mpr ⟨before, ht', rfl⟩

end Itasca
