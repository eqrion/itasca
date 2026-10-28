import Itasca.Runtime.Representation.StackLayout
import Itasca.Runtime.Equations
import Itasca.Runtime.Representation.Layout
import Itasca.Runtime.Platform.Alloc
import Itasca.Support.TypeTranslation

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

@[step] theorem compiler_width (ty : Itasca.types.ValueType) :
    runtime.value.width ty ⦃ word => word.val = width (Itasca.Translate.valueType ty) ⦄ := by
  cases ty <;> simp [runtime.value.width, Itasca.Translate.valueType, width, WP.spec_ok]

@[step] theorem operand_at (before : Slice U32) (depth : Usize)
    (positive : 0 < depth.val) (fits : depth.val ≤ before.val.length) :
    runtime.compiler.operand_at before depth ⦃ result =>
      result = .Ok (before.val[before.val.length - depth.val]'(by omega)) ⦄ := by
  have nonzero : depth ≠ 0#usize := by scalar_tac
  have bounded : ¬ depth > Slice.len before := by scalar_tac
  simp only [runtime.compiler.operand_at, nonzero, bounded, if_false]
  step as ⟨index, hi⟩
  step as ⟨value, hv⟩
  congr 1
  simpa [hi] using hv

@[step] theorem budget_push {A T : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (values : alloc.vec.Vec T) (value : T) (fits : values.val.length < Usize.max) :
    runtime.compiler.Budget.push ops budget values value ⦃ out =>
      (out.1 = .Ok () ∧ out.2.1 = budget ∧ out.2.2.val = values.val ++ [value]) ∨
      (out.1 = .Err .OutOfMemory ∧ out.2.2 = values ∧
        out.2.1.error = some .Allocation) ⦄ := by
  obtain ⟨answer, reserve⟩ := law.reserve_eq values 1#usize
  unfold runtime.compiler.Budget.push
  rw [reserve, bind_ok]
  cases answer with
  | false => simp [runtime.compiler.Budget.reject, WP.spec_ok]
  | true =>
    change (do
      let after ← alloc.vec.Vec.push values value
      pure (core.result.Result.Ok (), budget, after)) ⦃ out =>
        (out.1 = .Ok () ∧ out.2.1 = budget ∧ out.2.2.val = values.val ++ [value]) ∨
        (out.1 = .Err Itasca.error.VisitError.OutOfMemory ∧ out.2.2 = values ∧
          out.2.1.error = some .Allocation) ⦄
    step as ⟨after, appended⟩
    simp [appended]



@[step] theorem observe_value {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (before : alloc.vec.Vec U32) (height : U32) (ty : Itasca.code.StackType)
    (fits : before.val.length < Usize.max) :
    runtime.compiler.observe_value ops budget before height ty ⦃ out =>
      match out.1 with
      | .Ok _ => out.2.1 = budget ∧ out.2.2.1.val = before.val ++ [height] ∧
          out.2.2.2.val = height.val + compilerStackWidth ty
      | .Err _ => out.2.2.2 = height ⦄ := by
  unfold runtime.compiler.observe_value
  step with budget_push ops law budget before height fits as ⟨r, budget1, before1, hp⟩
  rcases hp with ⟨rfl, rfl, appended⟩ | ⟨rfl, rfl, rejected⟩
  · cases ty <;> simp only [runtime.compiler.stack_width] <;> step* <;> cases ‹Option U32› <;>
      simp_all [compilerStackWidth, core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca.Runtime.Code
