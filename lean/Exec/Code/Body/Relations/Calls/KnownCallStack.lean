import Exec.Code.Local.Relations.Common.KnownNumericStack
import Exec.Code.Body.Reader.Calls.ReaderCallEffects
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts

@[step] theorem apply_func_type_known (st : code.OpIterState) (ft : types.FuncType)
    (outer segment : List code.StackType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length) (known : ConcreteStack st.vals.val) :
    code.apply_func_type st ft ⦃ out => out.1 = .Ok () → ConcreteStack out.2.vals.val ⦄ := by
  have both := concreteStack_append.mp (values ▸ known)
  obtain ⟨check, checked, _⟩ := WP.spec_imp_exists (code.check_func_type.spec ft)
  unfold code.apply_func_type
  rw [checked]
  cases check with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok unit =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨⟨result, middle⟩, popped, _, _, rest, vals, restKnown⟩ := WP.spec_imp_exists
      (pop_types_concrete st outer segment (alloc.vec.Vec.deref ft.params) values base both.2)
    rw [popped]
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok unit =>
      simp only [bind_ok]
      step
      split
      · simp
      · step with code.push_types.spec middle (alloc.vec.Vec.deref ft.results)
          (by simp [alloc.vec.Vec.deref]; scalar_tac) as ⟨after, afterValues, _, _⟩
        intro success
        rw [afterValues, vals]
        exact concreteStack_append.mpr ⟨concreteStack_append.mpr ⟨both.1, restKnown⟩,
          by simp [alloc.vec.Vec.deref, ConcreteStack]⟩

theorem reader_call_known_wasm2 (st out : code.BodyState) (data : Slice U8) (env : module.Env)
    (index : U32) (outer segment : List code.StackType)
    (values : st.core.vals.val = outer ++ segment) (base : (Control.base st.core).val = outer.length)
    (known : ConcreteStack st.core.vals.val)
    (accepted : code.call_info st data env = .ok (.Ok index, out)) :
    ConcreteStack out.core.vals.val := by
  obtain ⟨⟨result, state⟩, read, sameValues, controls, post⟩ := WP.spec_imp_exists (code.take_index.spec st.core data)
  dsimp only at sameValues controls post
  cases result with
  | Err error => simp [code.call_info, read, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok idx =>
    by_cases bound : idx.val < env.func_types.val.length
    · have indexBound : (UScalar.cast .Usize idx).val < env.func_types.val.length := by simpa using bound
      obtain ⟨ft, indexed, lookup⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec env.func_types (UScalar.cast .Usize idx) indexBound)
      obtain ⟨⟨reply, after⟩, applied, effect⟩ := WP.spec_imp_exists
        (code.apply_func_type.realizes state ft outer segment (by simpa [sameValues] using values)
          (by simpa [Control.base, controls] using base))
      cases reply with
      | Err error => simp [code.call_info, read, lift, Nat.not_le_of_gt bound, indexed, applied,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
      | Ok unit =>
        cases unit
        obtain ⟨_, _, _, _, rest, afterValues, _, transfer⟩ := effect rfl
        dsimp only at afterValues transfer
        simp [code.call_info, read, lift, Nat.not_le_of_gt bound, indexed, applied,
          core.result.Result.Insts.CoreOpsTry.branch] at accepted
        obtain ⟨rfl, rfl⟩ := accepted
        have knowledge := apply_func_type_known state ft outer segment
          (by simpa [sameValues] using values) (by simpa [Control.base, controls] using base)
          (by simpa [sameValues] using known)
        rw [applied, WP.spec_ok] at knowledge
        exact knowledge rfl
    · simp [code.call_info, read, lift, Nat.le_of_not_gt bound,
        core.result.Result.Insts.CoreOpsTry.branch] at accepted


theorem reader_call_known_wasm1 (st out : code.OpIterState) (data : Slice U8) (env : module.Env)
    (index : U32) (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment) (base : (Control.base st).val = outer.length)
    (capacity : st.vals.val.length < Usize.max)
    (known : ConcreteStack st.vals.val)
    (accepted : code.read_call st data env = .ok (.Ok index, out)) :
    ConcreteStack out.vals.val := by
  obtain ⟨⟨result, state⟩, read, sameValues, controls, post⟩ := WP.spec_imp_exists (code.take_index.spec st data)
  dsimp only at sameValues controls post
  cases result with
  | Err error => simp [code.read_call, read, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok idx =>
    by_cases bound : idx.val < env.func_types.val.length
    · have indexBound : (UScalar.cast .Usize idx).val < env.func_types.val.length := by simpa using bound
      obtain ⟨ft, indexed, lookup⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec env.func_types (UScalar.cast .Usize idx) indexBound)
      obtain ⟨requirement, checked, resultLimit⟩ := WP.spec_imp_exists
        (code.require_single_result.spec (alloc.vec.Vec.deref ft.results))
      cases requirement with
      | Err error => simp [code.read_call, read, lift, Nat.not_le_of_gt bound, indexed, checked,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
      | Ok unit =>
        obtain ⟨⟨reply, next⟩, popped, _, _, rest, nextValues, shrink, transfer⟩ := WP.spec_imp_exists
          (code.pop_types.realizes state outer segment (alloc.vec.Vec.deref ft.params)
            (by simpa [sameValues] using values) (by simpa [Control.base, controls] using base))
        dsimp only at nextValues shrink transfer
        cases reply with
        | Err error => simp [code.read_call, read, lift, Nat.not_le_of_gt bound, indexed, checked, popped,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
        | Ok unit =>
          have resultLength : ft.results.val.length ≤ 1 := by simpa [alloc.vec.Vec.deref] using resultLimit
          have fits : next.vals.val.length + (alloc.vec.Vec.deref ft.results).val.length ≤ Usize.max := by
            simp only [nextValues, values, List.length_append, alloc.vec.Vec.deref] at *
            omega
          obtain ⟨finalState, pushed, finalValues, _, _⟩ := WP.spec_imp_exists
            (code.push_types.spec next (alloc.vec.Vec.deref ft.results) fits)
          simp [code.read_call, read, lift, Nat.not_le_of_gt bound, indexed, checked, popped, pushed,
            core.result.Result.Insts.CoreOpsTry.branch] at accepted
          obtain ⟨rfl, rfl⟩ := accepted
          have knowledge := pop_types_concrete state outer segment (alloc.vec.Vec.deref ft.params)
            (by simpa [sameValues] using values) (by simpa [Control.base, controls] using base)
            (concreteStack_append.mp (values ▸ known)).2
          rw [popped, WP.spec_ok] at knowledge
          obtain ⟨_, _, remainder, remainderValues, remainderKnown⟩ := knowledge
          rw [finalValues, remainderValues]
          exact concreteStack_append.mpr ⟨concreteStack_append.mpr
            ⟨(concreteStack_append.mp (values ▸ known)).1, remainderKnown⟩,
            by simp [alloc.vec.Vec.deref, ConcreteStack]⟩
    · simp [code.read_call, read, lift, Nat.le_of_not_gt bound,
        core.result.Result.Insts.CoreOpsTry.branch] at accepted

end Exec.Code
