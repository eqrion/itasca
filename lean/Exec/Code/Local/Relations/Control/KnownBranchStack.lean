import Exec.Code.Local.Relations.Common.KnownPopStack
namespace Exec.Code
open Aeneas Aeneas.Std
open Itasca

/-- Conditional branches retain a concrete physical stack for every resolved
multi-value label. No live-control premise is needed for the physical pops. -/
theorem wasm2_branch_if_concrete (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (outer segment : List code.StackType) (values : st.core.vals.val = outer ++ segment)
    (base : (Control.base st.core).val = outer.length) (shape : Control.Shape st.core)
    (aligned : st.blocks.val.length = st.core.ctrls.val.length) (known : ConcreteStack st.core.vals.val) :
    code.branch st data env true ⦃ out => out.1 = .Ok () → ConcreteStack out.2.core.vals.val ⦄ := by
  rw [code.branch.eq_core]
  unfold Wasm2.branchCore
  have knownParts : ConcreteStack outer ∧ ConcreteStack segment := concreteStack_append.mp (values ▸ known)
  step with code.read_multi_value_label.spec st data aligned
    as ⟨result, decoded, sameValues, sameControls, sameBlocks, _, _⟩
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok view =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, ↓reduceIte]
    step with pop_with_type_concrete decoded.core outer segment .I32
      (by simpa only [sameValues] using values) (by simpa only [Control.base, sameControls] using base) knownParts.2
      as ⟨condition, afterCondition, conditionControls, _, rest, conditionValues, conditionKnown⟩
    cases condition with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with pop_results_concrete afterCondition env view outer rest conditionValues
        (by simpa only [Control.base, conditionControls, sameControls] using base) conditionKnown
        as ⟨args, afterArgs, argsControls, _, tail, argsValues, argsKnown⟩
      cases args with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok unit =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, ↓reduceIte]
        have afterShape : Control.Shape afterArgs := shape.replace_operands
          (argsControls.trans (conditionControls.trans sameControls)) (by simp [argsValues, base])
        step with code.push_results.total afterArgs env view afterShape
          as ⟨answer, finalState, _, _, _, pushed⟩
        intro accepted
        obtain ⟨types, _, afterValues⟩ := pushed accepted
        rw [afterValues, argsValues]
        exact concreteStack_append.mpr ⟨concreteStack_append.mpr ⟨knownParts.1, argsKnown⟩, concrete_values types⟩
end Exec.Code
