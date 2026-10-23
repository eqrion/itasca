import Exec.Interp.Simd.Common.SimdShiftLoop
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Exec.Spec.Simd

def shiftOpcode (ty : Jnn) (kind : ShiftKind) : U32 :=
  match ty,kind with
  | .I8,.left => 107#u32 | .I8,.signedRight => 108#u32 | .I8,.unsignedRight => 109#u32
  | .I16,.left => 139#u32 | .I16,.signedRight => 140#u32 | .I16,.unsignedRight => 141#u32
  | .I32,.left => 171#u32 | .I32,.signedRight => 172#u32 | .I32,.unsignedRight => 173#u32
  | .I64,.left => 203#u32 | .I64,.signedRight => 204#u32 | .I64,.unsignedRight => 205#u32

def shiftWidth (ty : Jnn) : U32 :=
  match ty with | .I8 => 8#u32 | .I16 => 16#u32 | .I32 => 32#u32 | .I64 => 64#u32

theorem shiftWidth_val (ty : Jnn) : (shiftWidth ty).val=lsize (lanetype_Jnn ty) := by cases ty <;> rfl

@[step] theorem shift_lanes (ty : Jnn) (kind : ShiftKind) (x y : U128) :
    runtime.interp.simd.shift_lanes (shiftOpcode ty kind) x y ⦃ result =>
      ∀ j, j < 128/lsize (lanetype_Jnn ty) →
        laneBits (lsize (lanetype_Jnn ty)) j result.bv =
          shiftBits kind (laneBits (lsize (lanetype_Jnn ty)) j x.bv)
            ((UScalar.cast .U32 y).val % lsize (lanetype_Jnn ty)) ⦄ := by
  unfold runtime.interp.simd.shift_lanes
  have opcodeBound : 96 ≤ (shiftOpcode ty kind).val := by cases ty <;> cases kind <;> decide
  step as ⟨difference,differenceEq⟩
  step as ⟨quotient,quotientEq⟩
  have quotientBound : quotient.val < 32 := by
    cases ty <;> cases kind <;> simp only [shiftOpcode] at differenceEq <;> scalar_tac
  step as ⟨width,widthEq,widthBits⟩
  have actualWidth : width = shiftWidth ty := by
    apply UScalar.eq_of_val_eq
    cases ty <;> cases kind <;> simp only [shiftOpcode,shiftWidth] at * <;> scalar_tac
  subst width
  simp only [lift,bind_ok]
  have positive : 0 < (shiftWidth ty).val := by cases ty <;> decide
  have bounded : (shiftWidth ty).val ≤ 64 := by cases ty <;> decide
  step as ⟨amount,amountEq⟩
  apply WP.spec_mono (shift_lanes_loop kind (shiftOpcode ty kind) (shiftWidth ty) amount x 0#u128 0#u32
    positive bounded (by scalar_tac)
    (by cases ty <;> cases kind <;> decide) (by cases ty <;> decide)
    (by intro j bound; change j < 0 at bound; omega))
  intro result lanes
  rw [amountEq] at lanes
  cases ty <;> with_unfolding_all exact lanes
end Exec.Interp.Simd
