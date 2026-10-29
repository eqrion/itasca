import Itasca.Runtime.Interp.Numeric.Float.FloatInstructionBasic
import Itasca.Runtime.Interp.Numeric.Float.FloatInstructionComparison
import Itasca.Runtime.Interp.Numeric.Float.FloatTruncInstruction
import Itasca.Runtime.Interp.Relations.ScalarDispatch

/-!
Floating-point opcode dispatch and its complete instruction effect. The dispatcher selects the separately proved arithmetic, comparison and conversion instruction cases.
-/

/-! ## Float Instruction -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std Platform

/-- Every scalar float opcode returns a bounded permitted source result or its exact numeric trap. -/
theorem scalar_float_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (op : Abs.Float.Instruction) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode op) a b ⦃ result =>
      FloatScalarOutcome op a b result ⦄ := by
  cases op with
  | unary ty operation =>
    cases ty <;> cases operation
    all_goals first
      | exact scalar_f32_abs_instruction ops a b
      | exact scalar_f32_neg_instruction ops a b
      | exact scalar_f32_ceil_instruction ops correct a b
      | exact scalar_f32_floor_instruction ops correct a b
      | exact scalar_f32_trunc_instruction ops correct a b
      | exact scalar_f32_nearest_instruction ops correct a b
      | exact scalar_f32_sqrt_instruction ops correct a b
      | exact scalar_f64_abs_instruction ops a b
      | exact scalar_f64_neg_instruction ops a b
      | exact scalar_f64_ceil_instruction ops correct a b
      | exact scalar_f64_floor_instruction ops correct a b
      | exact scalar_f64_trunc_instruction ops correct a b
      | exact scalar_f64_nearest_instruction ops correct a b
      | exact scalar_f64_sqrt_instruction ops correct a b
  | binary ty operation =>
    cases ty <;> cases operation
    all_goals first
      | exact scalar_f32_add_instruction ops correct a b
      | exact scalar_f32_sub_instruction ops correct a b
      | exact scalar_f32_mul_instruction ops correct a b
      | exact scalar_f32_div_instruction ops correct a b
      | exact scalar_f32_min_instruction ops a b
      | exact scalar_f32_max_instruction ops a b
      | exact scalar_f32_copysign_instruction ops a b
      | exact scalar_f64_add_instruction ops correct a b
      | exact scalar_f64_sub_instruction ops correct a b
      | exact scalar_f64_mul_instruction ops correct a b
      | exact scalar_f64_div_instruction ops correct a b
      | exact scalar_f64_min_instruction ops a b
      | exact scalar_f64_max_instruction ops a b
      | exact scalar_f64_copysign_instruction ops a b
  | compare ty operation =>
    cases ty <;> cases operation
    all_goals first
      | exact scalar_f32_eq_instruction ops a b
      | exact scalar_f32_ne_instruction ops a b
      | exact scalar_f32_lt_instruction ops a b
      | exact scalar_f32_gt_instruction ops a b
      | exact scalar_f32_le_instruction ops a b
      | exact scalar_f32_ge_instruction ops a b
      | exact scalar_f64_eq_instruction ops a b
      | exact scalar_f64_ne_instruction ops a b
      | exact scalar_f64_lt_instruction ops a b
      | exact scalar_f64_gt_instruction ops a b
      | exact scalar_f64_le_instruction ops a b
      | exact scalar_f64_ge_instruction ops a b
  | convert source target sign =>
    cases source <;> cases target <;> cases sign
    all_goals first
      | exact scalar_f32_convert_i32_s_instruction ops correct a b
      | exact scalar_f32_convert_i32_u_instruction ops correct a b
      | exact scalar_f32_convert_i64_s_instruction ops correct a b
      | exact scalar_f32_convert_i64_u_instruction ops correct a b
      | exact scalar_f64_convert_i32_s_instruction ops correct a b
      | exact scalar_f64_convert_i32_u_instruction ops correct a b
      | exact scalar_f64_convert_i64_s_instruction ops correct a b
      | exact scalar_f64_convert_i64_u_instruction ops correct a b
  | truncate source target sign sat =>
    cases source <;> cases target <;> cases sign <;> cases sat
    all_goals first
      | exact scalar_i32_trunc_f32_s_instruction ops a b
      | exact scalar_i32_trunc_f32_u_instruction ops a b
      | exact scalar_i32_trunc_f64_s_instruction ops a b
      | exact scalar_i32_trunc_f64_u_instruction ops a b
      | exact scalar_i64_trunc_f32_s_instruction ops a b
      | exact scalar_i64_trunc_f32_u_instruction ops a b
      | exact scalar_i64_trunc_f64_s_instruction ops a b
      | exact scalar_i64_trunc_f64_u_instruction ops a b
      | exact scalar_i32_trunc_sat_f32_s_instruction ops a b
      | exact scalar_i32_trunc_sat_f32_u_instruction ops a b
      | exact scalar_i32_trunc_sat_f64_s_instruction ops a b
      | exact scalar_i32_trunc_sat_f64_u_instruction ops a b
      | exact scalar_i64_trunc_sat_f32_s_instruction ops a b
      | exact scalar_i64_trunc_sat_f32_u_instruction ops a b
      | exact scalar_i64_trunc_sat_f64_s_instruction ops a b
      | exact scalar_i64_trunc_sat_f64_u_instruction ops a b
  | reinterpretFloat source =>
    cases source
    all_goals first
      | exact scalar_i64_reinterpret_f64_instruction ops a b
      | exact scalar_i32_reinterpret_f32_instruction ops a b
  | reinterpretInt source =>
    cases source
    all_goals first
      | exact scalar_f64_reinterpret_i64_instruction ops a b
      | exact scalar_f32_reinterpret_i32_instruction ops a b
  | promote => exact scalar_f64_promote_f32_instruction ops a b
  | demote => exact scalar_f32_demote_f64_instruction ops correct a b

end Itasca.Runtime.Interp

end

/-! ## Float Dispatch -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std Platform

theorem scalar_float_dispatch {F : Type} (ops : runtime.platform.FloatOps F)
    (op : Abs.Float.Instruction) (a b : U64) :
    runtime.interp.int.scalar ops (floatOpcode op) a b =
      runtime.interp.float.scalar ops (floatOpcode op) a b := by
  unfold runtime.interp.int.scalar
  rw [show lift (UScalar.cast .U32 a) = Result.ok (UScalar.cast .U32 a) from rfl, bind_ok]
  rw [show lift (UScalar.cast .U32 b) = Result.ok (UScalar.cast .U32 b) from rfl, bind_ok]
  cases op with
  | unary ty operation => cases ty <;> cases operation <;> with_unfolding_all rfl
  | binary ty operation => cases ty <;> cases operation <;> with_unfolding_all rfl
  | compare ty operation => cases ty <;> cases operation <;> with_unfolding_all rfl
  | convert source target sign => cases source <;> cases target <;> cases sign <;> with_unfolding_all rfl
  | truncate source target sign sat => cases source <;> cases target <;> cases sign <;> cases sat <;> with_unfolding_all rfl
  | reinterpretFloat source => cases source <;> with_unfolding_all rfl
  | reinterpretInt source => cases source <;> with_unfolding_all rfl
  | promote | demote => with_unfolding_all rfl

theorem execute_float_effect {F : Type} (floats : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect floats)
    (exec : runtime.interp.Execution) (base : Usize) (op : Abs.Float.Instruction) (dst left right : U32)
    (hl : base.val + left.val < exec.slots.length)
    (hr : base.val + right.val < exec.slots.length)
    (hd : base.val + dst.val < exec.slots.length) :
    runtime.interp.execute_scalar floats exec base (floatOpcode op) dst left right ⦃ out =>
      ∃ numeric, FloatScalarOutcome op exec.slots.val[base.val + left.val]! exec.slots.val[base.val + right.val]! numeric ∧
        ScalarEffect exec (base.val + dst.val) numeric out ⦄ := by
  obtain ⟨numeric, equation, exactResult⟩ := WP.spec_imp_exists
    (scalar_float_instruction floats correct op exec.slots.val[base.val + left.val]! exec.slots.val[base.val + right.val]!)
  rw [← scalar_float_dispatch] at equation
  apply WP.spec_mono (execute_scalar_effect floats exec base (floatOpcode op) dst left right hl hr hd numeric equation)
  exact fun _ effect => ⟨numeric, exactResult, effect⟩
end Itasca.Runtime.Interp

end
