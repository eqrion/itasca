import Exec.Code.Local.Relations.Common.KnownNumericStack
import Exec.Code.Body.Reader.Local.ReaderLocalEffects
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_local_set_known (st out : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (index : U32) (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment) (base : (Control.base st).val = outer.length)
    (known : ConcreteStack st.vals.val)
    (accepted : code.read_local_set st data ctx = .ok (.Ok index, out)) :
    ConcreteStack out.vals.val := by
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
      obtain ⟨remainder, _, _, remaining, shrink, nextKnown⟩ :=
        pop_with_type_known state next outer segment ty (.Ok raw)
          (by simpa [stateValues] using values) (by simpa [Control.base, controls] using base)
          (by simpa [stateValues] using known) popped
      simp [code.read_local_set, read, popped, core.result.Result.Insts.CoreOpsTry.branch] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      exact nextKnown

theorem reader_local_tee_known (st out : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (index : U32) (capacity : st.vals.val.length < Usize.max) (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment) (base : (Control.base st).val = outer.length)
    (known : ConcreteStack st.vals.val)
    (accepted : code.read_local_tee st data ctx = .ok (.Ok index, out)) :
    ConcreteStack out.vals.val := by
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
      obtain ⟨remainder, _, _, remaining, shrink, nextKnown⟩ :=
        pop_with_type_known state next outer segment ty (.Ok raw)
          (by simpa [stateValues] using values) (by simpa [Control.base, controls] using base)
          (by simpa [stateValues] using known) popped
      have nextCapacity : next.vals.val.length < Usize.max := by
        simp only [remaining, values, List.length_append] at *
        omega
      obtain ⟨finalState, pushed, finalValues, _, _⟩ := WP.spec_imp_exists
        (code.push_val.spec next (.Val ty) nextCapacity)
      simp [code.read_local_tee, read, popped, pushed, core.result.Result.Insts.CoreOpsTry.branch] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      rw [finalValues]
      exact concreteStack_append.mpr ⟨nextKnown, by simp [ConcreteStack]⟩

end Exec.Code
