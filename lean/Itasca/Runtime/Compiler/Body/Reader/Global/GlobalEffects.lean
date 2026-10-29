import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEffects

/-!
Successful global reads return the declared global type and append exactly that concrete operand to the physical validator stack.

Main declarations: `reader_global_get_effect` and `reader_global_set_effect`. A direct consumer is `Compiler.Body.Reader.Acceptance.ReachedSimpleAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
/-- Successful global reads return the declared global type and append exactly
that concrete operand to the physical validator stack. -/
theorem reader_global_get_effect (st out : code.OpIterState) (data : Slice U8) (env : module.Env)
    (index : U32) (capacity : st.vals.val.length < Usize.max)
    (accepted : code.read_global_get st data env = .ok (.Ok index, out)) :
    ∃ ty : types.GlobalType, env.global_types.val[index.val]? = some ty ∧
      out.vals.val = st.vals.val ++ [.Val ty.valtype] := by
  obtain ⟨⟨result, state⟩, read, values, controls, post⟩ := WP.spec_imp_exists (code.take_global.spec st data env)
  dsimp only at values controls post
  cases result with
  | Err error =>
    simp [code.read_global_get, read, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨idx, ty⟩ := pair
    obtain ⟨_, bound, lookup⟩ := post
    obtain ⟨next, pushed, nextValues, _, _⟩ := WP.spec_imp_exists
      (code.push_val.spec state (.Val ty.valtype) (by simpa [values] using capacity))
    simp [code.read_global_get, read, core.result.Result.Insts.CoreOpsTry.branch,
      pushed, bind_ok, Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    exact ⟨ty, by simpa [List.getElem?_eq_getElem bound] using congrArg some lookup,
      by simpa [values] using nextValues⟩

/-- A live, concrete global write consumes exactly the global's declared type. -/
theorem reader_global_set_effect (st out : code.OpIterState) (data : Slice U8) (env : module.Env)
    (index : U32) (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment) (base : (Control.base st).val = outer.length)
    (monomorphic : Control.polymorphic st = false) (known : ConcreteStack segment)
    (accepted : code.read_global_set st data env = .ok (.Ok index, out)) :
    ∃ ty : types.GlobalType, env.global_types.val[index.val]? = some ty ∧ ty.mutability = .Var ∧
      st.vals.val = out.vals.val ++ [.Val ty.valtype] := by
  obtain ⟨⟨result, state⟩, read, stateValues, controls, post⟩ := WP.spec_imp_exists (code.take_global.spec st data env)
  dsimp only at stateValues controls post
  cases result with
  | Err error =>
    simp [code.read_global_set, read, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨idx, ty⟩ := pair
    obtain ⟨_, bound, lookup⟩ := post
    cases mutable : ty.mutability with
    | Const =>
      simp [code.read_global_set, read, mutable, core.result.Result.Insts.CoreOpsTry.branch] at accepted
    | Var =>
      obtain ⟨⟨popResult, next⟩, popped, _, _, rest, nextValues, popEffect⟩ := WP.spec_imp_exists
        (code.pop_with_type.segment state outer segment ty.valtype (by simpa [stateValues] using values)
          (by simpa [Control.base, controls] using base))
      dsimp only at nextValues popEffect
      cases popResult with
      | Err error =>
        simp [code.read_global_set, read, popped, mutable, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
      | Ok raw =>
        have poly : Control.polymorphic state = false := by simpa [Control.polymorphic, controls] using monomorphic
        rw [poly] at popEffect
        have segmentShape := typed_pop_exact known popEffect
        simp [code.read_global_set, read, popped, mutable, core.result.Result.Insts.CoreOpsTry.branch] at accepted
        obtain ⟨rfl, rfl⟩ := accepted
        exact ⟨ty, by simpa [List.getElem?_eq_getElem bound] using congrArg some lookup, mutable,
          by simp [values, nextValues, segmentShape, List.append_assoc]⟩

end Itasca.Runtime.Compiler
