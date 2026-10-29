import Itasca.Runtime.Interp.Simd.Integer.ShiftBits
import Itasca.Runtime.Spec.Simd.Shift

/-!
Integer lane shifts from scalar words through the lane loop. Bit extraction and the final source-dispatch result remain separate for their distinct consumers.
-/

/-! ## Simd Shift Word -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
open Itasca.Runtime.Spec.Simd

def shiftCode (kind : ShiftKind) : Nat :=
  match kind with | .left => 11 | .signedRight => 12 | .unsignedRight => 13

theorem shift_word (kind : ShiftKind) (op width amount : U32) (value : U64)
    (bits : BitVec width.val) (input : value.bv = bits.setWidth 64)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64) (amountBound : amount.val < width.val)
    (operation : op.val=shiftCode kind) :
    (match op with
      | 11#uscalar => value <<< amount
      | 12#uscalar => do
          let signedValue ← runtime.interp.simd.signed value width
          let shifted ← signedValue >>> amount
          Result.ok (IScalar.hcast .U64 shifted)
      | _ => value >>> amount) ⦃ result =>
        result.bv.setWidth width.val = shiftBits kind bits amount.val ⦄ := by
  have truncated : value.bv.setWidth width.val = bits := by rw [input,BitVec.setWidth_setWidth_of_le _ widthBound,BitVec.setWidth_eq]
  cases kind with
  | left =>
    have eq : op=11#u32 := UScalar.eq_of_val_eq operation
    subst op
    with_unfolding_all change (value <<< amount) ⦃ _ ⦄
    step as ⟨result,valueEq,bitsEq⟩
    simp only [shiftBits,bitsEq,BitVec.setWidth_shiftLeft_of_le widthBound,truncated]
  | signedRight =>
    have eq : op=12#u32 := UScalar.eq_of_val_eq operation
    subst op
    with_unfolding_all change (do
      let s ← runtime.interp.simd.signed value width
      let shifted ← s >>> amount
      Result.ok (IScalar.hcast .U64 shifted)) ⦃ _ ⦄
    step with signed_bits value width positive widthBound as ⟨signedValue,signedEq⟩
    step as ⟨shifted,shiftedEq,shiftedBits⟩
    simp only [shiftBits]
    simp only [IScalar.hcast_bv_eq, UScalarTy.U64_numBits_eq, IScalarTy.I64_numBits_eq, BitVec.signExtend_eq]
    rw [shiftedBits,signedEq,truncated,shift_right_signed_widen _ _ _ positive widthBound]
  | unsignedRight =>
    have eq : op=13#u32 := UScalar.eq_of_val_eq operation
    subst op
    with_unfolding_all change (value >>> amount) ⦃ _ ⦄
    step as ⟨result,valueEq,bitsEq⟩
    simp only [shiftBits]
    rw [bitsEq,input,shift_right_widen _ _ _ widthBound]
end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Shift Loop -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

@[step] theorem shift_lanes_loop (kind : ShiftKind) (op width amount : U32) (x initial : U128) (i : U32)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64) (amountBound : amount.val < width.val)
    (operation : op.val%32=shiftCode kind) (position : i.val ≤ 128/width.val)
    (initializedPrefix : ∀ j, j < i.val → laneBits width.val j initial.bv = shiftBits kind (laneBits width.val j x.bv) amount.val) :
    runtime.interp.simd.shift_lanes_loop op x width amount initial i ⦃ result =>
      ∀ j, j < 128/width.val → laneBits width.val j result.bv = shiftBits kind (laneBits width.val j x.bv) amount.val ⦄ := by
  unfold runtime.interp.simd.shift_lanes_loop
  apply loop.spec_decr_nat (fun p => 128/width.val-p.2.val)
    (fun p => p.2.val ≤ 128/width.val ∧
      ∀ j, j < p.2.val → laneBits width.val j p.1.bv = shiftBits kind (laneBits width.val j x.bv) amount.val)
  · rintro ⟨current,index⟩ ⟨indexBound,initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.shift_lanes_loop.body
    step as ⟨count,countEq⟩
    split
    · rename_i more
      have less : index.val < 128/width.val := by scalar_tac
      have range := lane_range width.val index.val less
      step with lane_bits x width index positive widthBound (by omega) as ⟨value,input⟩
      step as ⟨selected,selectedEq⟩
      step with shift_word kind selected width amount value (laneBits width.val index.val x.bv) input
        positive widthBound amountBound (selectedEq.trans operation) as ⟨shifted,shiftedEq⟩
      step with put_lanes current width index shifted positive widthBound range as ⟨updated,same,other⟩
      have countBound : 128/width.val ≤ 128 := Nat.div_le_self _ _
      step as ⟨next,nextEq⟩
      refine ⟨?_,?_,?_⟩
      · omega
      · intro j bound
        by_cases eq : j=index.val
        · subst j; exact same.trans shiftedEq
        · rw [other j (lane_range _ _ (by omega)) eq]
          exact initialized j (by omega)
      · omega
    · have finished : index.val=128/width.val := by scalar_tac
      simpa [finished] using initialized
  · exact ⟨position,initializedPrefix⟩
end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Shift -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def shiftOpcode (ty : Jnn) (kind : ShiftKind) : U32 :=
  match ty,kind with
  | .I8,.left => 107#u32 | .I8,.signedRight => 108#u32 | .I8,.unsignedRight => 109#u32
  | .I16,.left => 139#u32 | .I16,.signedRight => 140#u32 | .I16,.unsignedRight => 141#u32
  | .I32,.left => 171#u32 | .I32,.signedRight => 172#u32 | .I32,.unsignedRight => 173#u32
  | .I64,.left => 203#u32 | .I64,.signedRight => 204#u32 | .I64,.unsignedRight => 205#u32

def shiftWidth (ty : Jnn) : U32 :=
  match ty with | .I8 => 8#u32 | .I16 => 16#u32 | .I32 => 32#u32 | .I64 => 64#u32

theorem shift_width_val (ty : Jnn) : (shiftWidth ty).val=lsize (lanetype_Jnn ty) := by cases ty <;> rfl

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
end Itasca.Runtime.Interp.Simd

end
