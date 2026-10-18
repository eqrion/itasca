import Exec.Interp.Simd.Common.SimdUnarySigns
import Exec.Spec.SimdBitmask
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Exec.Spec.Simd SpecExt.Builtins
@[step] theorem bitmask_lanes_sound (ty : Jnn) (x : U128) :
    runtime.interp.simd.integer_unary_lanes (unaryOpcode ty .bitmask) x
      ⦃ result => Step_pure [.VCONST .V128 (.mk_uN x.val),bitmaskSource ty]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN result.val))] ⦄ := by
  apply WP.spec_mono (integer_unary_lanes ty .bitmask x)
  intro result outcome
  let signs := unarySigns (lsize (lanetype_Jnn ty)) x.bv (128/lsize (lanetype_Jnn ty))
  have mask := unary_signs_get (lsize (lanetype_Jnn ty)) x.bv (128/lsize (lanetype_Jnn ty))
    (by cases ty <;> decide) (by cases ty <;> decide) (by cases ty <;> decide)
  have source := bitmask_step ty x.bv signs mask
  change result = UScalar.cast .U128 (⟨signs⟩ : U32) at outcome
  subst result
  have value : (UScalar.cast .U128 (⟨signs⟩ : U32)).val = signs.toNat := by
    simp only [UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le signs.isLt (by decide))
  rw [value]
  exact source

theorem bitmask_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (unaryOpcode ty .bitmask) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.integer_unary_lanes (unaryOpcode ty .bitmask) x)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> unfold runtime.interp.simd.simd unaryOpcode <;> with_unfolding_all rfl
end Exec.Interp.Simd
