import Exec.Code.Body.Reader.Common.ReaderValues
import Exec.Code.Body.Reader.Local.ReaderWasm2Local
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Successful local reads return the declared local type and append exactly
that concrete operand to the physical validator stack. -/
theorem reader_local_get_effect (st out : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (index : U32) (capacity : st.vals.val.length < Usize.max)
    (accepted : code.read_local_get st data ctx = .ok (.Ok index, out)) :
    ∃ ty : types.ValueType, ctx.locals.val[index.val]? = some ty ∧
      out.vals.val = st.vals.val ++ [.Val ty] := by
  obtain ⟨⟨result, state⟩, read, values, controls, post⟩ := WP.spec_imp_exists (code.take_local.spec st data ctx)
  dsimp only at values controls post
  cases result with
  | Err error =>
    simp [code.read_local_get, read, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨idx, ty⟩ := pair
    obtain ⟨_, bound, lookup⟩ := post
    obtain ⟨next, pushed, nextValues, _, _⟩ := WP.spec_imp_exists
      (code.push_val.spec state (.Val ty) (by simpa [values] using capacity))
    simp [code.read_local_get, read, core.result.Result.Insts.CoreOpsTry.branch,
      pushed, bind_ok, Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    exact ⟨ty, by simpa [List.getElem?_eq_getElem bound] using congrArg some lookup,
      by simpa [values] using nextValues⟩

theorem typed_pop_exact {segment rest : List code.StackType} {ty value}
    (known : ConcreteStack segment)
    (effect : StackSemantics.TypedPopResult false segment ty (.Ok value) rest) :
    segment = rest ++ [.Val ty] := by
  obtain ⟨popped, accepted⟩ := effect
  cases popped with
  | explicit =>
    cases value with
    | Bot => exact False.elim (known .Bot (by simp) rfl)
    | Val raw =>
      change Translate.valueType ty = Translate.valueType raw at accepted
      have equal : ty = raw := Translate.valueType_injective accepted
      simp [equal]

/-- A live, concrete local write consumes exactly the local's declared type. -/
theorem reader_local_set_effect (st out : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (index : U32) (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment) (base : (Control.base st).val = outer.length)
    (monomorphic : Control.polymorphic st = false) (known : ConcreteStack segment)
    (accepted : code.read_local_set st data ctx = .ok (.Ok index, out)) :
    ∃ ty : types.ValueType, ctx.locals.val[index.val]? = some ty ∧
      st.vals.val = out.vals.val ++ [.Val ty] := by
  obtain ⟨⟨result, state⟩, read, stateValues, controls, post⟩ := WP.spec_imp_exists (code.take_local.spec st data ctx)
  dsimp only at stateValues controls post
  cases result with
  | Err error =>
    simp [code.read_local_set, read, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨idx, ty⟩ := pair
    obtain ⟨_, bound, lookup⟩ := post
    obtain ⟨⟨popResult, next⟩, popped, _, _, rest, nextValues, popEffect⟩ := WP.spec_imp_exists
      (code.pop_with_type.segment state outer segment ty (by simpa [stateValues] using values)
        (by simpa [Control.base, controls] using base))
    dsimp only at nextValues popEffect
    cases popResult with
    | Err error =>
      simp [code.read_local_set, read, popped, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
    | Ok raw =>
      have poly : Control.polymorphic state = false := by simpa [Control.polymorphic, controls] using monomorphic
      rw [poly] at popEffect
      have segmentShape := typed_pop_exact known popEffect
      simp [code.read_local_set, read, popped, core.result.Result.Insts.CoreOpsTry.branch] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      exact ⟨ty, by simpa [List.getElem?_eq_getElem bound] using congrArg some lookup,
        by simp [values, nextValues, segmentShape, List.append_assoc]⟩

/-- A live, concrete local write consumes exactly the local's declared type. -/
theorem reader_local_tee_effect (st out : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (index : U32) (capacity : st.vals.val.length < Usize.max) (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment) (base : (Control.base st).val = outer.length)
    (monomorphic : Control.polymorphic st = false) (known : ConcreteStack segment)
    (accepted : code.read_local_tee st data ctx = .ok (.Ok index, out)) :
    ∃ ty : types.ValueType, ctx.locals.val[index.val]? = some ty ∧
      ∃ rest, st.vals.val = rest ++ [.Val ty] ∧ out.vals.val = st.vals.val := by
  obtain ⟨⟨result, state⟩, read, stateValues, controls, post⟩ := WP.spec_imp_exists (code.take_local.spec st data ctx)
  dsimp only at stateValues controls post
  cases result with
  | Err error =>
    simp [code.read_local_tee, read, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨idx, ty⟩ := pair
    obtain ⟨_, bound, lookup⟩ := post
    obtain ⟨⟨popResult, next⟩, popped, _, _, rest, nextValues, popEffect⟩ := WP.spec_imp_exists
      (code.pop_with_type.segment state outer segment ty (by simpa [stateValues] using values)
        (by simpa [Control.base, controls] using base))
    dsimp only at nextValues popEffect
    cases popResult with
    | Err error =>
      simp [code.read_local_tee, read, popped, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
    | Ok raw =>
      have poly : Control.polymorphic state = false := by simpa [Control.polymorphic, controls] using monomorphic
      rw [poly] at popEffect
      have segmentShape := typed_pop_exact known popEffect
      have nextCapacity : next.vals.val.length < Usize.max := by
        have shrink : next.vals.val.length ≤ st.vals.val.length := by
          simp only [nextValues, values, segmentShape, List.length_append, List.length_singleton]
          omega
        omega
      obtain ⟨finalState, pushed, finalValues, _, _⟩ := WP.spec_imp_exists
        (code.push_val.spec next (.Val ty) nextCapacity)
      simp [code.read_local_tee, read, popped, pushed, core.result.Result.Insts.CoreOpsTry.branch] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      refine ⟨ty, by simpa [List.getElem?_eq_getElem bound] using congrArg some lookup,
        outer ++ rest, ?_, ?_⟩
      · simp [values, segmentShape, List.append_assoc]
      · simp [finalValues, nextValues, values, segmentShape, List.append_assoc]

end Exec.Code
