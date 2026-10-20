import Exec.Abs.Float.ChosenDescriptor
import Exec.Interp.Numeric.Float.FloatInstruction
import Exec.Interp.Numeric.Float.FloatChosen
import Exec.Interp.Numeric.Float.FloatMinMaxChosen
import Exec.Interp.Numeric.Float.FloatResizeChosen
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt Exec.Spec Platform

def FloatChosenScalarOutcome (choices : SourceChoices) (occurrence : Nat)
    (op : Abs.Float.Instruction) (a b : U64)
    (result : core.result.Result U64 runtime.ExecError) : Prop :=
  match result with
  | .Ok value => op.ChosenResult choices occurrence (floatInput op.input a) (floatInput op.input b) (some value.val)
  | .Err (.Trap reason) => op.ChosenResult choices occurrence (floatInput op.input a) (floatInput op.input b) none ∧
      (reason = .IntegerOverflow ∨ reason = .InvalidConversionToInteger)
  | .Err _ => False

theorem scalar_float_forced {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) {choices : SourceChoices} (admissible : choices.Admissible)
    (occurrence : Nat) (op : Abs.Float.Instruction) (a b : U64)
    (forced : op.forcedNumeric = true) :
    runtime.interp.float.scalar ops (floatOpcode op) a b ⦃ result =>
      FloatChosenScalarOutcome choices occurrence op a b result ⦄ := by
  apply WP.spec_mono (scalar_float_instruction ops correct op a b)
  intro result source
  cases result with
  | Ok value =>
    simp only [FloatScalarOutcome] at source
    exact op.chosen_result_forced admissible occurrence source forced
  | Err error =>
    cases error
    all_goals try { exact False.elim source }
    exact ⟨op.chosen_result_forced admissible occurrence source.1 forced, source.2⟩

theorem scalar_float_numeric {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) {choices : SourceChoices}
    (numeric : choices.numeric = firstNumericChoice) (occurrence : Nat)
    (op : Abs.Float.Instruction) (a b : U64) (request : NumericRequest)
    (read : op.numericRequest (floatInput op.input a) (floatInput op.input b) = some request)
    (selected : runtime.interp.float.scalar ops (floatOpcode op) a b ⦃ result =>
      ∃ value, result = .Ok value ∧ ChosenNumeric firstNumericChoice occurrence request
        (some (Abs.Float.numberOfBits op.output value.val)) ⦄) :
    runtime.interp.float.scalar ops (floatOpcode op) a b ⦃ result =>
      FloatChosenScalarOutcome choices occurrence op a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_float_instruction ops correct op a b) selected)
  rintro result ⟨source, value, rfl, chosen⟩
  simp only [FloatScalarOutcome] at source
  change op.ChosenResult choices occurrence (floatInput op.input a) (floatInput op.input b) (some value.val)
  apply Abs.Float.Instruction.chosen_result_of_numeric source read
  simpa only [numeric,Option.map_some] using chosen

/-- The actual scalar dispatcher refines one fixed numeric policy at every
occurrence, including numeric traps and all supported scalar conversions. -/
theorem scalar_float_chosen_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) {choices : SourceChoices} (admissible : choices.Admissible)
    (numeric : choices.numeric = firstNumericChoice) (occurrence : Nat)
    (op : Abs.Float.Instruction) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode op) a b ⦃ result =>
      FloatChosenScalarOutcome choices occurrence op a b result ⦄ := by
  cases op with
  | unary ty operation =>
    cases ty <;> cases operation
    all_goals first
      | exact scalar_float_forced ops correct admissible occurrence _ a b rfl
      | exact scalar_float_numeric ops correct numeric occurrence _ a b _ rfl (scalar_f32_ceil_chosen ops correct occurrence a b)
      | exact scalar_float_numeric ops correct numeric occurrence _ a b _ rfl (scalar_f32_floor_chosen ops correct occurrence a b)
      | exact scalar_float_numeric ops correct numeric occurrence _ a b _ rfl (scalar_f32_trunc_chosen ops correct occurrence a b)
      | exact scalar_float_numeric ops correct numeric occurrence _ a b _ rfl (scalar_f32_nearest_chosen ops correct occurrence a b)
      | exact scalar_float_numeric ops correct numeric occurrence _ a b _ rfl (scalar_f32_sqrt_chosen ops correct occurrence a b)
      | exact scalar_float_numeric ops correct numeric occurrence _ a b _ rfl (scalar_f64_ceil_chosen ops correct occurrence a b)
      | exact scalar_float_numeric ops correct numeric occurrence _ a b _ rfl (scalar_f64_floor_chosen ops correct occurrence a b)
      | exact scalar_float_numeric ops correct numeric occurrence _ a b _ rfl (scalar_f64_trunc_chosen ops correct occurrence a b)
      | exact scalar_float_numeric ops correct numeric occurrence _ a b _ rfl (scalar_f64_nearest_chosen ops correct occurrence a b)
      | exact scalar_float_numeric ops correct numeric occurrence _ a b _ rfl (scalar_f64_sqrt_chosen ops correct occurrence a b)
  | binary ty operation =>
    cases ty <;> cases operation
    all_goals first
      | exact scalar_float_forced ops correct admissible occurrence _ a b rfl
      | exact scalar_float_numeric ops correct numeric occurrence _ a b _ rfl (scalar_f32_add_chosen ops correct occurrence a b)
      | exact scalar_float_numeric ops correct numeric occurrence _ a b _ rfl (scalar_f32_sub_chosen ops correct occurrence a b)
      | exact scalar_float_numeric ops correct numeric occurrence _ a b _ rfl (scalar_f32_mul_chosen ops correct occurrence a b)
      | exact scalar_float_numeric ops correct numeric occurrence _ a b _ rfl (scalar_f32_div_chosen ops correct occurrence a b)
      | exact scalar_float_numeric ops correct numeric occurrence _ a b _ rfl (scalar_f32_min_chosen ops occurrence a b)
      | exact scalar_float_numeric ops correct numeric occurrence _ a b _ rfl (scalar_f32_max_chosen ops occurrence a b)
      | exact scalar_float_numeric ops correct numeric occurrence _ a b _ rfl (scalar_f64_add_chosen ops correct occurrence a b)
      | exact scalar_float_numeric ops correct numeric occurrence _ a b _ rfl (scalar_f64_sub_chosen ops correct occurrence a b)
      | exact scalar_float_numeric ops correct numeric occurrence _ a b _ rfl (scalar_f64_mul_chosen ops correct occurrence a b)
      | exact scalar_float_numeric ops correct numeric occurrence _ a b _ rfl (scalar_f64_div_chosen ops correct occurrence a b)
      | exact scalar_float_numeric ops correct numeric occurrence _ a b _ rfl (scalar_f64_min_chosen ops occurrence a b)
      | exact scalar_float_numeric ops correct numeric occurrence _ a b _ rfl (scalar_f64_max_chosen ops occurrence a b)
  | compare ty operation => exact scalar_float_forced ops correct admissible occurrence _ a b rfl
  | convert source target sign => exact scalar_float_forced ops correct admissible occurrence _ a b rfl
  | truncate source target sign saturating => exact scalar_float_forced ops correct admissible occurrence _ a b rfl
  | reinterpretFloat source => exact scalar_float_forced ops correct admissible occurrence _ a b rfl
  | reinterpretInt source => exact scalar_float_forced ops correct admissible occurrence _ a b rfl
  | promote => exact scalar_float_numeric ops correct numeric occurrence _ a b _ rfl (scalar_f64_promote_f32_chosen ops occurrence a b)
  | demote => exact scalar_float_numeric ops correct numeric occurrence _ a b _ rfl (scalar_f32_demote_f64_chosen ops correct occurrence a b)
end Exec.Interp
