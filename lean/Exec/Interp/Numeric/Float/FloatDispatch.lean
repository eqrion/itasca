import Exec.Interp.Numeric.Float.FloatInstruction
import Exec.Interp.Relations.ScalarDispatch
namespace Exec.Interp
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
end Exec.Interp
