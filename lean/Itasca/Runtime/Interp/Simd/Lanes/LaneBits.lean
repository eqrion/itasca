import Itasca.Runtime.Interp.Simd.Lanes.Access

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
