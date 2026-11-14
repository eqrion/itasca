import Itasca.Runtime.Interp.Numeric.Integer.Int
import SpecExt.Builtins.Examples
import Itasca.Runtime.Spec.Simd.CompareInteger

/-!
Sections, each formerly its own module: Access, LaneBits, Splat, Packing, SplatSound.
-/

/-! ## Access -/

section

/-!
Runtime lane masks, extraction and insertion.

Main declarations: `mask` and `put`. A direct consumer is `Interp.Simd.Bitwise.Whole`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem mask (width : U32) (bound : width.val < 128) :
    runtime.interp.simd.mask width ⦃ result => result.val = 2^width.val - 1 ⦄ := by
  unfold runtime.interp.simd.mask
  step as ⟨power, powerEq, powerBits⟩
  have powerValue : power.val = 2^width.val := by
    rw [powerEq]
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    apply Nat.mod_eq_of_lt
    simp only [U128.size, U128.numBits, UScalarTy.U128_numBits_eq]
    exact Nat.pow_lt_pow_right (by decide) bound
  have positive : 1 ≤ power.val := by rw [powerValue]; exact Nat.one_le_pow _ _ (by decide)
  step
  scalar_tac

@[step] theorem lane (v : U128) (width index : U32)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64)
    (positionBound : width.val * index.val < 128) :
    runtime.interp.simd.lane v width index ⦃ result =>
      result.val = v.val / 2^(width.val * index.val) % 2^width.val ⦄ := by
  unfold runtime.interp.simd.lane
  step as ⟨position, positionEq⟩
  step as ⟨shifted, shiftedEq, shiftedBits⟩
  step with mask width (by omega) as ⟨maskValue, maskEq⟩
  simp only [lift, bind_ok, WP.spec_ok]
  rw [UScalar.cast_val_eq, UScalar.val_and, maskEq, Nat.and_two_pow_sub_one_eq_mod,
    shiftedEq, Nat.shiftRight_eq_div_pow, positionEq]
  apply Nat.mod_eq_of_lt
  exact lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
    (Nat.pow_le_pow_right (by decide) widthBound)

@[step] theorem put (v : U128) (width index : U32) (x : U64)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64)
    (positionBound : width.val * index.val < 128) :
    runtime.interp.simd.put v width index x ⦃ result =>
      result.bv =
        (v.bv &&& ~~~((BitVec.ofNat 128 (2^width.val-1)) <<< (width.val*index.val))) |||
        (((x.bv.setWidth 128) &&& (BitVec.ofNat 128 (2^width.val-1))) <<< (width.val*index.val)) ⦄ := by
  unfold runtime.interp.simd.put
  step as ⟨position, positionEq⟩
  step with mask width (by omega) as ⟨maskValue, maskEq⟩
  have maskBits : maskValue.bv = BitVec.ofNat 128 (2^width.val-1) := by
    rw [←maskEq]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    change maskValue.val = maskValue.val % 2^128
    exact (Nat.mod_eq_of_lt (by scalar_tac)).symm
  step as ⟨shiftedMask, shiftedMaskEq, shiftedMaskBits⟩
  simp only [lift,bind_ok]
  step as ⟨shiftedValue, shiftedValueEq, shiftedValueBits⟩
  simp only [WP.spec_ok,UScalar.bv_or,UScalar.bv_and,UScalar.bv_not,
    shiftedMaskBits,shiftedValueBits,maskBits,positionEq]
  rfl
end Itasca.Runtime.Interp.Simd

end

/-! ## LaneBits -/

section

/-!
Bit-level lane extraction and replacement.

Main declarations: `laneBits` and `writeLaneBits`. A direct consumer is `Interp.Simd.Lanes.Splat`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

def laneBits (width index : Nat) (v : BitVec 128) : BitVec width :=
  (v >>> (width*index)).setWidth width

def writeLaneBits (width index : Nat) (v : BitVec 128) (x : BitVec 64) : BitVec 128 :=
  (v &&& ~~~((BitVec.ofNat 128 (2^width-1)) <<< (width*index))) |||
    (((x.setWidth 128) &&& BitVec.ofNat 128 (2^width-1)) <<< (width*index))

theorem lane_bits_get (width index bit : Nat) (v : BitVec 128) :
    (laneBits width index v).getLsbD bit =
      (decide (bit < width) && v.getLsbD (width*index+bit)) := by
  simp only [laneBits, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]

theorem write_lane_bits_get (width index bit : Nat) (v : BitVec 128) (x : BitVec 64)
    (bound : bit < 128) :
    (writeLaneBits width index v x).getLsbD bit =
      if width*index ≤ bit ∧ bit < width*index+width then x.getLsbD (bit-width*index)
      else v.getLsbD bit := by
  simp only [writeLaneBits, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  by_cases inside : width*index ≤ bit ∧ bit < width*index+width
  · have below : bit-width*index < width := by omega
    have valid : bit-width*index < 128 := by omega
    simp [bound, inside, Nat.not_lt.mpr inside.1, below, valid]
  · by_cases before : bit < width*index
    · simp [bound, inside, before]
    · have after : ¬bit-width*index < width := by omega
      simp [bound, inside, before, after]

theorem lane_bits_write_same (width index : Nat) (v : BitVec 128) (x : BitVec 64)
    (range : width*index+width ≤ 128) :
    laneBits width index (writeLaneBits width index v x) = x.setWidth width := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit
  rw [lane_bits_get, BitVec.getLsbD_setWidth]
  by_cases valid : bit < width
  · rw [write_lane_bits_get width index _ v x (by omega)]
    simp [valid, show width*index ≤ width*index+bit by omega,
      show width*index+bit < width*index+width by omega]
  · simp [valid]

theorem lane_bits_write_other (width index other : Nat) (v : BitVec 128) (x : BitVec 64)
    (range : width*other+width ≤ 128) (different : other ≠ index) :
    laneBits width other (writeLaneBits width index v x) = laneBits width other v := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit
  rw [lane_bits_get, lane_bits_get]
  by_cases valid : bit < width
  · have outside : ¬(width*index ≤ width*other+bit ∧ width*other+bit < width*index+width) := by
      rcases Nat.lt_or_gt_of_ne different with less | greater
      · have order : width*(other+1) ≤ width*index := Nat.mul_le_mul_left _ less
        rw [Nat.mul_succ] at order
        omega
      · have order : width*(index+1) ≤ width*other := Nat.mul_le_mul_left _ greater
        rw [Nat.mul_succ] at order
        omega
    rw [write_lane_bits_get width index _ v x (by omega)]
    simp [outside]
  · simp [valid]

@[step] theorem put_lanes (v : U128) (width index : U32) (x : U64)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64)
    (range : width.val*index.val+width.val ≤ 128) :
    runtime.interp.simd.put v width index x ⦃ result =>
      laneBits width.val index.val result.bv = x.bv.setWidth width.val ∧
      ∀ other, width.val*other+width.val ≤ 128 → other ≠ index.val →
        laneBits width.val other result.bv = laneBits width.val other v.bv ⦄ := by
  apply WP.spec_mono (put v width index x positive widthBound (by omega))
  intro result bits
  change result.bv = writeLaneBits width.val index.val v.bv x.bv at bits
  constructor
  · exact (congrArg (laneBits width.val index.val) bits).trans
      (lane_bits_write_same _ _ _ _ range)
  · intro other bound different
    exact (congrArg (laneBits width.val other) bits).trans
      (lane_bits_write_other _ _ _ _ _ bound different)

end Itasca.Runtime.Interp.Simd

end

/-! ## Splat -/

section

/-!
Lane bounds and runtime scalar splatting.

Main declarations: `lane_range` and `splat`. A direct consumer is `Interp.Simd.Float.Binary`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem lane_range (width index : Nat) (bound : index < 128/width) :
    width*index+width ≤ 128 := by
  have order := Nat.mul_le_mul_left width bound
  have limit := Nat.mul_div_le 128 width
  rw [Nat.mul_succ] at order
  omega

@[step] theorem splat_loop (x : U64) (width : U32) (initial : U128) (i : U32)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64)
    (position : i.val ≤ 128/width.val)
    (initializedPrefix : ∀ j, j < i.val → laneBits width.val j initial.bv = x.bv.setWidth width.val) :
    runtime.interp.simd.splat_loop x width initial i ⦃ result =>
      ∀ j, j < 128/width.val → laneBits width.val j result.bv = x.bv.setWidth width.val ⦄ := by
  unfold runtime.interp.simd.splat_loop
  apply loop.spec_decr_nat (fun p => 128/width.val-p.2.val)
    (fun p => p.2.val ≤ 128/width.val ∧
      ∀ j, j < p.2.val → laneBits width.val j p.1.bv = x.bv.setWidth width.val)
  · rintro ⟨current, index⟩ ⟨indexBound, initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.splat_loop.body
    dsimp only
    step as ⟨count, countEq⟩
    split
    · rename_i more
      have less : index.val < 128/width.val := by scalar_tac
      have range := lane_range width.val index.val less
      step with put_lanes current width index x positive widthBound range as ⟨updated, same, other⟩
      have countBound : 128/width.val ≤ 128 := Nat.div_le_self _ _
      step as ⟨next, nextEq⟩
      refine ⟨?_, ?_, ?_⟩
      · omega
      · intro j bound
        by_cases eq : j = index.val
        · subst j; exact same
        · rw [other j (lane_range _ _ (by omega)) eq]
          exact initialized j (by omega)
      · omega
    · have finished : index.val = 128/width.val := by scalar_tac
      simpa [finished] using initialized
  · exact ⟨position, initializedPrefix⟩

@[step] theorem splat (x : U64) (width : U32)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64) :
    runtime.interp.simd.splat x width ⦃ result =>
      ∀ j, j < 128/width.val → laneBits width.val j result.bv = x.bv.setWidth width.val ⦄ := by
  exact splat_loop x width 0#u128 0#u32 positive widthBound (by simp) (by simp)

end Itasca.Runtime.Interp.Simd

end

/-! ## Packing -/

section

/-!
Relating packed lane bits to source vectors.

Main declarations: `lane_bits_to_nat` and `splat_packed`. A direct consumer is `Interp.Simd.Float.Binary`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem lane_bits_to_nat (width index : Nat) (v : BitVec 128) :
    (laneBits width index v).toNat = v.toNat / 2^(width*index) % 2^width := by
  simp only [laneBits, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem pack_lanes_of_lane_bits (ty : lanetype) (v : BitVec 128) (x : BitVec 64)
    (lanes : ∀ j, j < 128/lsize ty → laneBits (lsize ty) j v = x.setWidth (lsize ty)) :
    SpecExt.Builtins.packLanes ty
      (List.replicate (128/lsize ty) (SpecExt.Builtins.laneOfBits ty (x.setWidth (lsize ty)).toNat)) =
      v.toNat := by
  have eq := SpecExt.Builtins.pack_replicate_of_lanes ty (128/lsize ty) v.toNat
    (x.setWidth (lsize ty)).toNat (by
      intro j bound
      rw [←lane_bits_to_nat]
      exact congrArg BitVec.toNat (lanes j bound))
  have covers : lsize ty * (128/lsize ty) = 128 := by cases ty <;> decide
  rw [covers, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le (by rfl))] at eq
  exact eq

theorem splat_packed (ty : lanetype) (x : U64) (width : U32)
    (widthEq : width.val = lsize ty) :
    runtime.interp.simd.splat x width ⦃ result =>
      uN.mk_uN result.val = inv_lanes_ (.X ty (.mk_dim (128/lsize ty)))
        (List.replicate (128/lsize ty) (SpecExt.Builtins.laneOfBits ty (x.bv.setWidth (lsize ty)).toNat)) ⦄ := by
  apply WP.spec_mono (splat x width (by rw [widthEq]; cases ty <;> decide)
    (by rw [widthEq]; cases ty <;> decide))
  intro result lanes
  rw [widthEq] at lanes
  have eq := pack_lanes_of_lane_bits ty result.bv x.bv lanes
  exact congrArg uN.mk_uN eq.symm

end Itasca.Runtime.Interp.Simd

end

/-! ## SplatSound -/

section

/-!
Opcode, input and source correspondence for scalar splatting.

Main declarations: `splatOpcode` and `splatInput`. A direct consumer is `Interp.Simd.Execution.PureUnary`.
-/

set_option maxRecDepth 4096
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem splat_sound (ty : lanetype) (x : U64) (width : U32)
    (widthEq : width.val = lsize ty) :
    runtime.interp.simd.splat x width ⦃ result =>
      Step_pure [.CONST (unpack ty) (Spec.Simd.scalarInput ty x.bv), .VSPLAT (Spec.Simd.shapeOf ty)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (splat_packed ty x width widthEq)
  intro result packed
  exact Spec.Simd.splat_step ty x.bv result.bv packed

def splatOpcode (ty : lanetype) : U32 :=
  match ty with
  | .I8 => 15#u32
  | .I16 => 16#u32
  | .I32 => 17#u32
  | .I64 => 18#u32
  | .F32 => 19#u32
  | .F64 => 20#u32

def splatInput (ty : lanetype) (a : U128) : U64 :=
  match ty with
  | .I8 | .I16 | .I32 | .F32 => UScalar.cast .U64 (UScalar.cast .U32 a)
  | .I64 | .F64 => UScalar.cast .U64 a

def splatWidth (ty : lanetype) : U32 :=
  match ty with
  | .I8 => 8#u32
  | .I16 => 16#u32
  | .I32 | .F32 => 32#u32
  | .I64 | .F64 => 64#u32

theorem splat_width_val (ty : lanetype) : (splatWidth ty).val = lsize ty := by
  cases ty <;> rfl

theorem splat_lanes_eq (ty : lanetype) (a : U128) :
    runtime.interp.simd.splat_lanes (splatOpcode ty) a =
      (runtime.interp.simd.splat (splatInput ty a) (splatWidth ty)) := by
  cases ty <;> unfold runtime.interp.simd.splat_lanes splatOpcode splatInput splatWidth
  all_goals simp only [lift, bind_ok]
  all_goals try simp only [
    show (15#u32 - 15#u32) = Result.ok 0#u32 by with_unfolding_all rfl,
    show (16#u32 - 15#u32) = Result.ok 1#u32 by with_unfolding_all rfl,
    show (17#u32 - 15#u32) = Result.ok 2#u32 by with_unfolding_all rfl, bind_ok,
    show (8#u32 <<< 0#u32) = Result.ok 8#u32 by with_unfolding_all rfl,
    show (8#u32 <<< 1#u32) = Result.ok 16#u32 by with_unfolding_all rfl,
    show (8#u32 <<< 2#u32) = Result.ok 32#u32 by with_unfolding_all rfl]
  all_goals try simp only [bind_ok]
  case I8 =>
    with_unfolding_all change (Aeneas.Std.bind (Result.ok (UScalar.cast .U64 (UScalar.cast .U32 a), 8#u32))
      (fun p => (runtime.interp.simd.splat p.1 p.2)) = _)
    rw [bind_ok]
  case I16 =>
    with_unfolding_all change (Aeneas.Std.bind (Result.ok (UScalar.cast .U64 (UScalar.cast .U32 a), 16#u32))
      (fun p => (runtime.interp.simd.splat p.1 p.2)) = _)
    rw [bind_ok]
  case I32 =>
    with_unfolding_all change (Aeneas.Std.bind (Result.ok (UScalar.cast .U64 (UScalar.cast .U32 a), 32#u32))
      (fun p => (runtime.interp.simd.splat p.1 p.2)) = _)
    rw [bind_ok]
  case I64 =>
    with_unfolding_all change (Aeneas.Std.bind (Result.ok (UScalar.cast .U64 a, 64#u32))
      (fun p => (runtime.interp.simd.splat p.1 p.2)) = _)
    rw [bind_ok]
  case F32 =>
    with_unfolding_all change (Aeneas.Std.bind (Result.ok (UScalar.cast .U64 (UScalar.cast .U32 a), 32#u32))
      (fun p => (runtime.interp.simd.splat p.1 p.2)) = _)
    rw [bind_ok]
  case F64 =>
    with_unfolding_all change (Aeneas.Std.bind (Result.ok (UScalar.cast .U64 a, 64#u32))
      (fun p => (runtime.interp.simd.splat p.1 p.2)) = _)
    rw [bind_ok]

theorem splat_input_source (ty : lanetype) (a : U128) :
    Spec.Simd.scalarInput ty (splatInput ty a).bv =
      Spec.Simd.scalarInput ty (UScalar.cast .U64 a).bv := by
  have low32 : ((UScalar.cast .U64 (UScalar.cast .U32 a)).bv).setWidth 32 =
      ((UScalar.cast .U64 a).bv).setWidth 32 := by
    change ((a.bv.setWidth 32).setWidth 64).setWidth 32 = (a.bv.setWidth 64).setWidth 32
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  cases ty with
  | I64 | F64 => rfl
  | I8 | I16 | I32 =>
    exact congrArg (fun (b : BitVec 32) => num_.mk_num__0 .I32 (.mk_uN b.toNat)) low32
  | F32 =>
    exact congrArg (fun (b : BitVec 32) => num_.mk_num__1 .F32 (SpecExt.Builtins.floatOfBits 32 b.toNat)) low32

@[step] theorem splat_lanes_sound (ty : lanetype) (a : U128) :
    runtime.interp.simd.splat_lanes (splatOpcode ty) a ⦃ result =>
      Step_pure [.CONST (unpack ty) (Spec.Simd.scalarInput ty (UScalar.cast .U64 a).bv),
        .VSPLAT (Spec.Simd.shapeOf ty)] [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  rw [splat_lanes_eq]
  apply WP.spec_mono (splat_sound ty (splatInput ty a) (splatWidth ty) (splat_width_val ty))
  intro result source
  rw [splat_input_source] at source
  exact source

theorem splat_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : lanetype) (offset laneIndex : U32) (bits a b c : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (splatOpcode ty) offset laneIndex bits a b c memory =
      Aeneas.Std.bind (runtime.interp.simd.splat_lanes (splatOpcode ty) a)
        (fun result => Result.ok (core.result.Result.Ok result, memory)) := by
  cases ty <;> unfold runtime.interp.simd.simd splatOpcode <;> with_unfolding_all rfl

@[step] theorem splat_dispatch_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : lanetype) (offset laneIndex : U32) (bits a b c : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (splatOpcode ty) offset laneIndex bits a b c memory
      ⦃ result => ∃ value, result = (.Ok value, memory) ∧
        Step_pure [.CONST (unpack ty) (Spec.Simd.scalarInput ty (UScalar.cast .U64 a).bv),
          .VSPLAT (Spec.Simd.shapeOf ty)] [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [splat_dispatch_eq]
  step with splat_lanes_sound ty a as ⟨value, source⟩
  exact ⟨value, rfl, source⟩

end Itasca.Runtime.Interp.Simd

end
