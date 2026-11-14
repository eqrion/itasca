import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Equations.Bytecode
import Itasca.Generated.FunsCompiler
import Itasca.Runtime.Representation.Layout
import Itasca.Runtime.Platform.Laws
import Itasca.Support.Result

/-!
Compiler value widths and observed operand layouts.

Main declarations: `compiler_width` and `observe_value`. A direct consumer is `Compiler.Local.Relations.Function.CoreFunction`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem compiler_width (ty : Itasca.wasm_types.ValueType) :
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

@[step] theorem operand_at_total (before : Slice U32) (depth : Usize) :
    runtime.compiler.operand_at before depth ⦃ out =>
      ∀ word, out = .Ok word → word ∈ before.val ⦄ := by
  by_cases zero : depth = 0#usize
  · simp [runtime.compiler.operand_at, zero, WP.spec_ok]
  · by_cases large : depth > Slice.len before
    · simp [runtime.compiler.operand_at, zero, large, WP.spec_ok]
    · have positive : 0 < depth.val := by scalar_tac
      have fits : depth.val ≤ before.val.length := by scalar_tac
      step with operand_at before depth positive fits as ⟨out, exactValue⟩
      rename_i word success
      rw [success] at exactValue
      cases exactValue
      exact List.getElem_mem _

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



/-- A successful checked append determines the vector effect without a capacity premise. -/
theorem budget_push_success {A T : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget afterBudget : runtime.compiler.Budget A)
    (before after : alloc.vec.Vec T) (value : T)
    (success : runtime.compiler.Budget.push ops budget before value = .ok (.Ok (), afterBudget, after)) :
    afterBudget = budget ∧ after.val = before.val ++ [value] := by
  obtain ⟨answer, reserve⟩ := law.reserve_eq before 1#usize
  unfold runtime.compiler.Budget.push at success
  rw [reserve, bind_ok] at success
  cases answer with
  | false => simp [runtime.compiler.Budget.reject] at success
  | true =>
    simp only [uncurry_apply_pair, ↓reduceIte, alloc.vec.Vec.push] at success
    split at success
    · simp only [bind_ok] at success
      have output := Result.ok_injective success
      have hb := congrArg (fun out => out.2.1) output
      have hv := congrArg (fun out => out.2.2.val) output
      exact ⟨hb.symm, by simpa using hv.symm⟩
    · simp only [bind_fail, fail_not_ok] at success

/-- A normally returning addition determines its mathematical sum, without
assuming the absence of overflow beforehand. -/
theorem control_add_success {ty : UScalarTy} {left right out : UScalar ty}
    (success : (left + right : Result (UScalar ty)) = .ok out) : out.val = left.val + right.val := by
  have spec := UScalar.add_equiv left right
  simp only [success] at spec
  exact spec.2.1

/-- Every normal checked append either keeps the vector or appends its value. -/
theorem budget_push_code_result {A T : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget afterBudget : runtime.compiler.Budget A)
    (before after : alloc.vec.Vec T) (value : T)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.Budget.push ops budget before value = .ok (status, afterBudget, after)) :
    after.val = before.val ∨ after.val = before.val ++ [value] := by
  obtain ⟨answer, reserve⟩ := law.reserve_eq before 1#usize
  unfold runtime.compiler.Budget.push at accepted
  rw [reserve, bind_ok] at accepted
  cases answer with
  | false =>
    simp only [uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte, runtime.compiler.Budget.reject,
      bind_ok, Result.ok.injEq, Prod.mk.injEq] at accepted
    exact Or.inl (congrArg (fun v : alloc.vec.Vec T => v.val) accepted.2.2).symm
  | true =>
    simp only [uncurry_apply_pair, ↓reduceIte, alloc.vec.Vec.push] at accepted
    split at accepted
    · simp only [bind_ok, Result.ok.injEq, Prod.mk.injEq] at accepted
      apply Or.inr
      simpa only [alloc.vec.Vec.from_val, List.concat_eq_append] using
        (congrArg (fun v : alloc.vec.Vec T => v.val) accepted.2.2).symm
    · simp only [bind_fail, fail_not_ok] at accepted

/-- An available bounded reserve request makes the actual compiler append
succeed with the exact appended vector and unchanged budget. -/
theorem budget_push_available {A T : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (values : alloc.vec.Vec T) (value : T)
    (fits : values.val.length < Usize.max) (request : values.val.length + 1 ≤ bound) :
    runtime.compiler.Budget.push ops budget values value ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = budget ∧ out.2.2.val = values.val ++ [value] ⦄ := by
  have reserve := available T values 1#usize (by simpa using request)
  unfold runtime.compiler.Budget.push
  rw [reserve,bind_ok]
  change (do
    let after ← alloc.vec.Vec.push values value
    pure (core.result.Result.Ok (),budget,after)) ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = budget ∧ out.2.2.val = values.val ++ [value] ⦄
  step as ⟨after,appended⟩
  exact appended

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

/-- Invert an ordinary result of an extracted monadic bind. -/
theorem initializer_bind_success {T U : Type} {input : Result T} {next : T → Result U}
    {out : U} (success : (input >>= next) = .ok out) :
    ∃ value, input = .ok value ∧ next value = .ok out := by
  change Aeneas.Std.bind input next = .ok out at success
  cases input with
  | ret value => exact ⟨value, rfl, by simpa only [bind_ok] using success⟩
  | vis event continuation => simp only [bind_vis] at success; exact (vis_not_ok success).elim
  | div => simp only [bind_div] at success; exact (div_not_ok success).elim

/-- Partial correctness for actual loops with a decreasing successful body.
This theorem makes no termination claim for a failing or divergent body. -/
theorem initializer_loop_success {S O : Type} (body : S → Result (ControlFlow S O))
    (measure : S → Nat) (inv : S → Prop) (post : O → Prop)
    (sound : ∀ state, inv state → ∀ flow, body state = .ok flow →
      match flow with
      | .cont next => inv next ∧ measure next < measure state
      | .done out => post out)
    (state : S) (initial : inv state) (out : O) (success : loop body state = .ok out) : post out := by
  suffices ∀ n state, measure state = n → inv state → loop body state = .ok out → post out by
    exact this (measure state) state rfl initial success
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro current hmeasure hcurrent returned
    rw [loop.eq_def] at returned
    obtain ⟨flow, step, rest⟩ := initializer_bind_success returned
    have effect := sound current hcurrent flow step
    cases flow with
    | done answer =>
      have same := Result.ok_injective rest
      subst answer
      exact effect
    | cont next =>
      exact ih (measure next) (by simpa [hmeasure] using effect.2) next rfl effect.1 rest

end Itasca.Runtime.Compiler
