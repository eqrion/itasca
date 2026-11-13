import «wasm2.0»
import Mathlib.Tactic
import Mathlib.Data.List.Rotate
import Mathlib.Data.Nat.Log
import SpecExt.Builtins.Float.Decoding
import Mathlib.Data.Nat.Basic

/-!
Sections, each formerly its own module: Lanes, EncodingLemmas, Bitwise, Rotations, Counts, BitwiseVector, LaneLaws, LaneView, LaneMap, Misc, Examples.
-/

/-! ## Lanes -/

section

namespace SpecExt.Builtins

theorem unpackLanes_length (ty : lanetype) (count bits : Nat) :
    (unpackLanes ty count bits).length = count := by
  induction count generalizing bits with
  | zero => rfl
  | succ count ih => simp only [unpackLanes, List.length_cons, ih]

end SpecExt.Builtins

end

/-! ## EncodingLemmas -/

section

/-! Integer encoding roundtrips and lengths. Truncation is explicit: arbitrary
naturals roundtrip modulo the selected width; valid inputs roundtrip exactly. -/

namespace SpecExt.Builtins

theorem integerBits_length (width value : Nat) :
    (integerBits width value).length = width := by
  induction width with
  | zero => rfl
  | succ width ih => simp only [integerBits, List.length_cons, ih]

theorem integerBytes_length (count value : Nat) :
    (integerBytes count value).length = count := by
  induction count generalizing value with
  | zero => rfl
  | succ count ih => simp only [integerBytes, List.length_cons, ih]

theorem integerOfBits_integerBits (width value : Nat) :
    integerOfBits (integerBits width value) = value % 2 ^ width := by
  induction width with
  | zero => simp [integerBits, integerOfBits, Nat.mod_one]
  | succ width ih =>
    simp only [integerBits, integerOfBits, integerBits_length, ih]
    rw [Nat.mod_pow_succ, Nat.mul_comm, Nat.add_comm]

theorem integerOfBytes_integerBytes (count value : Nat) :
    integerOfBytes (integerBytes count value) = value % 256 ^ count := by
  induction count generalizing value with
  | zero => simp [integerBytes, integerOfBytes, Nat.mod_one]
  | succ count ih =>
    simp only [integerBytes, integerOfBytes, ih]
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ count) 256, Nat.mod_mul]

theorem integerBits_roundtrip {width value : Nat} (h : value < 2 ^ width) :
    integerOfBits (integerBits width value) = value := by
  rw [integerOfBits_integerBits, Nat.mod_eq_of_lt h]

theorem integerBytes_roundtrip {count value : Nat} (h : value < 256 ^ count) :
    integerOfBytes (integerBytes count value) = value := by
  rw [integerOfBytes_integerBytes, Nat.mod_eq_of_lt h]

end SpecExt.Builtins

end

/-! ## Bitwise -/

section

/-! The prose's most-significant-first bit-list operations agree with natural
bitwise operations on the low width bits. -/
namespace SpecExt.Builtins

theorem bitCoefficient (value index : Nat) :
    value / 2 ^ index % 2 = (value.testBit index).toNat := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h := Nat.mod_lt (value / 2 ^ index) (by decide : 0 < 2)
  by_cases hz : value / 2 ^ index % 2 = 1
  · simp [hz]
  · have : value / 2 ^ index % 2 = 0 := by omega
    simp [this]

theorem bitCoefficient_and (a b index : Nat) :
    (a &&& b) / 2 ^ index % 2 = (a / 2 ^ index % 2) * (b / 2 ^ index % 2) := by
  simp only [bitCoefficient, Nat.testBit_and]
  cases a.testBit index <;> cases b.testBit index <;> rfl

theorem bitCoefficient_or (a b index : Nat) :
    (a ||| b) / 2 ^ index % 2 = max (a / 2 ^ index % 2) (b / 2 ^ index % 2) := by
  simp only [bitCoefficient, Nat.testBit_or]
  cases a.testBit index <;> cases b.testBit index <;> rfl

theorem bitCoefficient_xor (a b index : Nat) :
    (a ^^^ b) / 2 ^ index % 2 = ((a / 2 ^ index % 2) + (b / 2 ^ index % 2)) % 2 := by
  simp only [bitCoefficient, Nat.testBit_xor]
  cases a.testBit index <;> cases b.testBit index <;> rfl

theorem integerBits_and (width a b : Nat) :
    List.zipWith (fun (.mk_bit x) (.mk_bit y) => bit.mk_bit (x * y))
      (integerBits width a) (integerBits width b) = integerBits width (a &&& b) := by
  induction width with
  | zero => rfl
  | succ width ih => simp only [integerBits, List.zipWith_cons_cons, ih, bitCoefficient_and]

theorem integerBits_or (width a b : Nat) :
    List.zipWith (fun (.mk_bit x) (.mk_bit y) => bit.mk_bit (max x y))
      (integerBits width a) (integerBits width b) = integerBits width (a ||| b) := by
  induction width with
  | zero => rfl
  | succ width ih => simp only [integerBits, List.zipWith_cons_cons, ih, bitCoefficient_or]

theorem integerBits_xor (width a b : Nat) :
    List.zipWith (fun (.mk_bit x) (.mk_bit y) => bit.mk_bit ((x + y) % 2))
      (integerBits width a) (integerBits width b) = integerBits width (a ^^^ b) := by
  induction width with
  | zero => rfl
  | succ width ih => simp only [integerBits, List.zipWith_cons_cons, ih, bitCoefficient_xor]

theorem iand_value (width a b : Nat) :
    iand_ width (.mk_uN a) (.mk_uN b) = .mk_uN ((a &&& b) % 2 ^ width) := by
  simp only [iand_, ibits_, proj_uN_0, integerBits_and, inv_ibits_, integerOfBits_integerBits]

theorem ior_value (width a b : Nat) :
    ior_ width (.mk_uN a) (.mk_uN b) = .mk_uN ((a ||| b) % 2 ^ width) := by
  simp only [ior_, ibits_, proj_uN_0, integerBits_or, inv_ibits_, integerOfBits_integerBits]

theorem ixor_value (width a b : Nat) :
    ixor_ width (.mk_uN a) (.mk_uN b) = .mk_uN ((a ^^^ b) % 2 ^ width) := by
  simp only [ixor_, ibits_, proj_uN_0, integerBits_xor, inv_ibits_, integerOfBits_integerBits]

end SpecExt.Builtins

end

/-! ## Rotations -/

section

namespace SpecExt.Builtins

theorem integerBits_get (width value index : Nat) (bound : index < width) :
    (integerBits width value)[index]'(by rw [integerBits_length]; exact bound) =
      .mk_bit ((value.testBit (width - 1 - index)).toNat) := by
  induction width generalizing index with
  | zero => omega
  | succ width ih =>
    cases index with
    | zero => simp [integerBits, bitCoefficient]
    | succ index =>
      have inner : index < width := by omega
      simpa only [integerBits, List.getElem_cons_succ, Nat.add_sub_cancel,
        show width - (index + 1) = width - 1 - index by omega] using ih index inner

theorem integerBits_getMsb (width : Nat) (bits : BitVec width) (index : Nat) (bound : index < width) :
    (integerBits width bits.toNat)[index]'(by rw [integerBits_length]; exact bound) =
      .mk_bit ((bits.getMsbD index).toNat) := by
  rw [integerBits_get width bits.toNat index bound]
  simp [BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD, bound]

/-- Rotating the prose's most-significant-first list rotates the represented
bitvector in the same direction. -/
theorem integerBits_rotateLeft (width : Nat) (bits : BitVec width) (shift : Nat) :
    (integerBits width bits.toNat).rotate shift = integerBits width (bits.rotateLeft shift).toNat := by
  apply List.ext_getElem
  · simp only [List.length_rotate, integerBits_length]
  · intro index left right
    have bound : index < width := by simpa only [integerBits_length] using right
    rw [List.getElem_rotate]
    rw [integerBits_getMsb _ _ _ (by rw [integerBits_length]; exact Nat.mod_lt _ (by omega)),
      integerBits_getMsb _ _ _ bound]
    simp only [integerBits_length, BitVec.getMsbD_rotateLeft, bound, decide_true, Bool.true_and, Nat.add_comm]

theorem integerBits_rotateRight (width : Nat) (bits : BitVec width) (shift : Nat) :
    (integerBits width bits.toNat).rotate (width - shift % width) =
      integerBits width (bits.rotateRight shift).toNat := by
  apply List.ext_getElem
  · simp only [List.length_rotate, integerBits_length]
  · intro index left right
    have bound : index < width := by simpa only [integerBits_length] using right
    have positive : 0 < width := by omega
    have shiftBound := Nat.mod_lt shift positive
    rw [List.getElem_rotate]
    rw [integerBits_getMsb _ _ _ (by rw [integerBits_length]; exact Nat.mod_lt _ (by omega)),
      integerBits_getMsb _ _ _ bound]
    simp only [integerBits_length, BitVec.getMsbD_rotateRight, bound, decide_true, Bool.true_and]
    split
    · have same : index + (width - shift % width) = width + index - shift % width := by omega
      rw [same]
    · have same : index + (width - shift % width) = width + (index - shift % width) := by omega
      have small : index - shift % width < width := by omega
      rw [same]
      simp only [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt small, Nat.mod_mod]

theorem irotl_bitvec (width : Nat) (bits : BitVec width) (shift : Nat) :
    irotl_ width (.mk_uN bits.toNat) (.mk_uN shift) = .mk_uN (bits.rotateLeft shift).toNat := by
  unfold irotl_ ibits_ inv_ibits_
  simp only [proj_uN_0]
  have rotate := List.rotate_eq_drop_append_take_mod (l := integerBits width bits.toNat) (n := shift)
  rw [integerBits_length] at rotate
  rw [← rotate, integerBits_rotateLeft, integerBits_roundtrip (bits.rotateLeft shift).isLt]

theorem irotr_bitvec (width : Nat) (bits : BitVec width) (shift : Nat) :
    irotr_ width (.mk_uN bits.toNat) (.mk_uN shift) = .mk_uN (bits.rotateRight shift).toNat := by
  unfold irotr_ ibits_ inv_ibits_
  simp only [proj_uN_0]
  rw [← List.rotate_eq_drop_append_take (by rw [integerBits_length]; omega),
    integerBits_rotateRight, integerBits_roundtrip (bits.rotateRight shift).isLt]

end SpecExt.Builtins

end

/-! ## Counts -/

section

namespace SpecExt.Builtins

/-- Exposing the low bit reconciles the prose's big-endian list with Rust's
low-bit recurrences for population and trailing-zero counts. -/
theorem integerBits_lsb (width value : Nat) :
    integerBits (width + 1) value = integerBits width (value / 2) ++ [.mk_bit (value % 2)] := by
  induction width with
  | zero => simp [integerBits]
  | succ width ih =>
    simp only [integerBits, List.cons_append, ← Nat.div_div_eq_div_mul, ih]
    congr 2
    rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]

theorem population_append (left right : List bit) :
    population (left ++ right) = population left + population right := by
  induction left with
  | nil => simp [population]
  | cons value rest ih => cases value; simp [population, ih, Nat.add_assoc]

theorem leadingZeros_zero (width : Nat) : leadingZeros (integerBits width 0) = width := by
  induction width with
  | zero => rfl
  | succ width ih => simp [integerBits, leadingZeros, ih, Nat.add_comm]

/-- The leading-zero list definition is the usual width-minus-log formula. -/
theorem leadingZeros_bits (width value : Nat) (bounded : value < 2 ^ width) :
    leadingZeros (integerBits width value) = if value = 0 then width else width - Nat.log 2 value - 1 := by
  by_cases zero : value = 0
  · subst value; simp [leadingZeros_zero]
  · simp only [zero, if_false]
    induction width with
    | zero => simp at bounded; contradiction
    | succ width ih =>
      by_cases lower : value < 2 ^ width
      · have digit : value / 2 ^ width % 2 = 0 := by simp [Nat.div_eq_of_lt lower]
        have logarithm : Nat.log 2 value < width := Nat.log_lt_of_lt_pow zero lower
        simp only [integerBits, digit, leadingZeros, ih lower]
        omega
      · have power : 2 ^ (width + 1) = 2 ^ width * 2 := pow_succ _ _
        have digit : value / 2 ^ width = 1 := by
          apply Nat.div_eq_of_lt_le
          · omega
          · omega
        have logarithm : Nat.log 2 value = width := Nat.log_eq_of_pow_le_of_lt_pow (by omega) bounded
        simp only [integerBits, digit, show 1 % 2 = 1 from rfl, leadingZeros, logarithm]
        omega

theorem leadingZeros_le_length (bits : List bit) : leadingZeros bits ≤ bits.length := by
  induction bits with
  | nil => simp [leadingZeros]
  | cons value rest ih =>
    cases value with
    | mk_bit value => cases value <;> simp [leadingZeros] <;> omega

theorem population_bits_le (width value : Nat) : population (integerBits width value) ≤ width := by
  induction width generalizing value with
  | zero => simp [integerBits, population]
  | succ width ih =>
    rw [integerBits_lsb, population_append]
    have prior := ih (value / 2)
    have digit := Nat.mod_lt value (by decide : 0 < 2)
    simp only [population, Nat.add_zero]
    omega

end SpecExt.Builtins

end

/-! ## BitwiseVector -/

section

namespace SpecExt.Builtins

theorem integerBits_not {n : Nat} (bits : BitVec n) (width : Nat)
    (bound : width ≤ n) :
    (integerBits width bits.toNat).map (fun (.mk_bit x) => bit.mk_bit (1-x)) =
      integerBits width (~~~bits).toNat := by
  induction width with
  | zero => rfl
  | succ width ih =>
    simp only [integerBits, List.map_cons, ih (by omega)]
    congr 1
    simp only [bitCoefficient, BitVec.testBit_toNat, BitVec.getLsbD_not,
      show width < n by omega, decide_true, Bool.true_and]
    cases bits.getLsbD width <;> rfl

theorem inot_bitvec {n : Nat} (bits : BitVec n) :
    inot_ n (.mk_uN bits.toNat) = .mk_uN (~~~bits).toNat := by
  simp only [inot_, ibits_, proj_uN_0, integerBits_not bits n (by omega),
    inv_ibits_, integerOfBits_integerBits]
  rw [Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le (by omega))]

theorem iand_bitvec {n : Nat} (a b : BitVec n) :
    iand_ n (.mk_uN a.toNat) (.mk_uN b.toNat) = .mk_uN (a &&& b).toNat := by
  rw [iand_value, ←BitVec.toNat_and, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le (by omega))]

theorem ior_bitvec {n : Nat} (a b : BitVec n) :
    ior_ n (.mk_uN a.toNat) (.mk_uN b.toNat) = .mk_uN (a ||| b).toNat := by
  rw [ior_value, ←BitVec.toNat_or, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le (by omega))]

theorem ixor_bitvec {n : Nat} (a b : BitVec n) :
    ixor_ n (.mk_uN a.toNat) (.mk_uN b.toNat) = .mk_uN (a ^^^ b).toNat := by
  rw [ixor_value, ←BitVec.toNat_xor, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le (by omega))]

theorem iandnot_bitvec {n : Nat} (a b : BitVec n) :
    iandnot_ n (.mk_uN a.toNat) (.mk_uN b.toNat) = .mk_uN (a &&& ~~~b).toNat := by
  simp only [iandnot_, inot_bitvec, iand_bitvec]

theorem ibitselect_bitvec {n : Nat} (a b c : BitVec n) :
    ibitselect_ n (.mk_uN a.toNat) (.mk_uN b.toNat) (.mk_uN c.toNat) =
      .mk_uN ((a &&& c) ||| (b &&& ~~~c)).toNat := by
  simp only [ibitselect_, iandnot_bitvec, iand_bitvec, ior_bitvec]

end SpecExt.Builtins

end

/-! ## LaneLaws -/

section

namespace SpecExt.Builtins
open Float

theorem laneBits_laneOfBits (ty : lanetype) (bits : Nat) (bound : bits < 2^lsize ty) :
    laneBits ty (laneOfBits ty bits) = bits := by
  cases ty with
  | F32 => exact float_bits_roundtrip_32 bits bound
  | F64 => exact float_bits_roundtrip_64 bits bound
  | _ => rfl

theorem unpackLanes_getElem? (ty : lanetype) (count bits index : Nat) :
    (unpackLanes ty count bits)[index]? =
      if index < count then some (laneOfBits ty (bits / 2^(lsize ty*index) % 2^lsize ty)) else none := by
  induction count generalizing bits index with
  | zero => simp [unpackLanes]
  | succ count ih =>
    cases index with
    | zero => simp [unpackLanes]
    | succ index =>
      simp only [unpackLanes, List.getElem?_cons_succ, ih, Nat.succ_lt_succ_iff,
        Nat.mul_succ, Nat.pow_add, Nat.div_div_eq_div_mul]
      rw [Nat.mul_comm (2^lsize ty) (2^(lsize ty*index))]


theorem pack_unpackLanes (ty : lanetype) (count bits : Nat) :
    packLanes ty (unpackLanes ty count bits) = bits % 2^(lsize ty*count) := by
  induction count generalizing bits with
  | zero => simp only [unpackLanes,packLanes,Nat.mul_zero,pow_zero,Nat.mod_one]
  | succ count ih =>
    simp only [unpackLanes,packLanes,laneBits_laneOfBits _ _ (Nat.mod_lt _ (by positivity)),ih]
    rw [Nat.mul_succ,Nat.pow_add,Nat.mul_comm (2^(lsize ty*count)) (2^lsize ty),Nat.mod_mul]
end SpecExt.Builtins

end

/-! ## LaneView -/

section

namespace SpecExt.Builtins

theorem unpackLanes_eq_replicate (ty : lanetype) (count bits value : Nat)
    (lanes : ∀ j, j < count → bits / 2^(lsize ty*j) % 2^lsize ty = value) :
    unpackLanes ty count bits = List.replicate count (laneOfBits ty value) := by
  apply List.ext_getElem?
  intro j
  rw [unpackLanes_getElem?]
  by_cases valid : j < count
  · simp [valid, lanes j valid]
  · simp [valid]

theorem pack_replicate_of_lanes (ty : lanetype) (count bits value : Nat)
    (lanes : ∀ j, j < count → bits / 2^(lsize ty*j) % 2^lsize ty = value) :
    packLanes ty (List.replicate count (laneOfBits ty value)) = bits % 2^(lsize ty*count) := by
  rw [←unpackLanes_eq_replicate ty count bits value lanes, pack_unpackLanes]

end SpecExt.Builtins

end

/-! ## LaneMap -/

section

namespace SpecExt.Builtins

theorem unpackLanes_eq_map (ty : lanetype) (count bits : Nat) (values : Nat → Nat)
    (lanes : ∀ j, j < count → bits/2^(lsize ty*j)%2^lsize ty = values j) :
    unpackLanes ty count bits = (List.range count).map (fun j => laneOfBits ty (values j)) := by
  apply List.ext_getElem?
  intro j
  rw [unpackLanes_getElem?]
  by_cases valid : j < count
  · simp [List.getElem?_map,List.getElem?_range,valid,lanes j valid]
  · simp [List.getElem?_map,List.getElem?_range,valid]

theorem pack_map_of_lanes (ty : lanetype) (count bits : Nat) (values : Nat → Nat)
    (lanes : ∀ j, j < count → bits/2^(lsize ty*j)%2^lsize ty = values j) :
    packLanes ty ((List.range count).map (fun j => laneOfBits ty (values j))) = bits%2^(lsize ty*count) := by
  rw [←unpackLanes_eq_map ty count bits values lanes,pack_unpackLanes]

end SpecExt.Builtins

end

/-! ## Misc -/

section

namespace SpecExt.Builtins

/-- Pair chunking preserves the original sequence when flattened. -/
theorem flatten_inv_concat (X : Type) :
    (xs : List X) → (inv_concat_ X xs).flatten = xs
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
      simp [inv_concat_, flatten_inv_concat X rest]

end SpecExt.Builtins

end

/-! ## Examples -/

section

/-! Kernel-checked integer vectors: signed boundaries, masked shift counts,
MSB-first bits, saturation, and Q15's exceptional minimum-times-minimum case.
No evaluation bypasses the kernel. Floating-point examples belong to M7. -/

namespace SpecExt.Builtins.Examples

example : lanes_ (.X .I64 (.mk_dim 2)) (.mk_uN 18446744073709551617) =
    [.mk_lane__0 .I64 (.mk_uN 1), .mk_lane__0 .I64 (.mk_uN 1)] := by decide
example : inv_lanes_ (.X .I32 (.mk_dim 4))
    [.mk_lane__0 .I32 (.mk_uN 1), .mk_lane__0 .I32 (.mk_uN 2),
     .mk_lane__0 .I32 (.mk_uN 3), .mk_lane__0 .I32 (.mk_uN 4)] =
    .mk_uN 316912650112397582603894390785 := by decide
example : lanes_ (.X .F64 (.mk_dim 2)) (.mk_uN 9223372036854775808) =
    [.mk_lane__1 .F64 (.NEG (.SUBNORM 0)),
     .mk_lane__1 .F64 (.POS (.SUBNORM 0))] := by decide

example : ibits_ 8 (.mk_uN 129) =
    [.mk_bit 1, .mk_bit 0, .mk_bit 0, .mk_bit 0,
     .mk_bit 0, .mk_bit 0, .mk_bit 0, .mk_bit 1] := by decide
example : inv_ibits_ 4 [.mk_bit 1, .mk_bit 0, .mk_bit 1, .mk_bit 0] = .mk_uN 10 := by decide
example : s33_to_u32 (.mk_sN 4294967295) = .mk_uN 4294967295 := by decide
example : truncz (Rat.mk' (-7) 2) = -3 := by decide
example : truncz (Rat.mk' 7 2) = 3 := by decide
example : truncz (Rat.mk' (-1) 2) = 0 := by decide
example : extend__ 8 32 .S (.mk_uN 128) = .mk_uN 4294967168 := by decide
example : extend__ 8 32 .S (.mk_uN 127) = .mk_uN 127 := by decide
example : extend__ 8 32 .U (.mk_uN 255) = .mk_uN 255 := by decide
example : wrap__ 64 32 (.mk_uN 4294967297) = .mk_uN 1 := by decide
example : narrow__ 16 8 .S (.mk_uN 256) = .mk_uN 127 := by decide
example : narrow__ 16 8 .S (.mk_uN 65280) = .mk_uN 128 := by decide
example : narrow__ 16 8 .U (.mk_uN 65535) = .mk_uN 0 := by decide
example : narrow__ 16 8 .U (.mk_uN 256) = .mk_uN 255 := by decide
example : narrow__ 16 8 .U (.mk_uN 127) = .mk_uN 127 := by decide
example : iclz_ 32 (.mk_uN 0) = .mk_uN 32 := by decide
example : ictz_ 64 (.mk_uN 0) = .mk_uN 64 := by decide
example : iclz_ 32 (.mk_uN 1) = .mk_uN 31 := by decide
example : ictz_ 32 (.mk_uN 2147483648) = .mk_uN 31 := by decide
example : ipopcnt_ 64 (.mk_uN 18446744073709551615) = .mk_uN 64 := by decide
example : iand_ 8 (.mk_uN 170) (.mk_uN 204) = .mk_uN 136 := by decide
example : ior_ 8 (.mk_uN 170) (.mk_uN 204) = .mk_uN 238 := by decide
example : ixor_ 8 (.mk_uN 170) (.mk_uN 204) = .mk_uN 102 := by decide
example : inot_ 8 (.mk_uN 170) = .mk_uN 85 := by decide
example : irev_ 8 (.mk_uN 19) = .mk_uN 200 := by decide
example : iandnot_ 8 (.mk_uN 170) (.mk_uN 204) = .mk_uN 34 := by decide
example : ibitselect_ 8 (.mk_uN 170) (.mk_uN 85) (.mk_uN 15) = .mk_uN 90 := by decide
example : ishl_ 32 (.mk_uN 2147483649) (.mk_uN 33) = .mk_uN 2 := by decide
example : ishr_ 32 .S (.mk_uN 4294967293) (.mk_uN 1) = .mk_uN 4294967294 := by decide
example : ishr_ 32 .U (.mk_uN 4294967293) (.mk_uN 1) = .mk_uN 2147483646 := by decide
example : ishr_ 64 .S (.mk_uN 9223372036854775808) (.mk_uN 64) =
    .mk_uN 9223372036854775808 := by decide
example : irotl_ 8 (.mk_uN 129) (.mk_uN 9) = .mk_uN 3 := by decide
example : irotr_ 8 (.mk_uN 129) (.mk_uN 9) = .mk_uN 192 := by decide
example : iavgr_ 8 .U (.mk_uN 0) (.mk_uN 1) = .mk_uN 1 := by decide
example : iavgr_ 8 .U (.mk_uN 255) (.mk_uN 255) = .mk_uN 255 := by decide
example : iq15mulr_sat_ 16 .S (.mk_uN 32768) (.mk_uN 32768) = .mk_uN 32767 := by decide
example : iq15mulr_sat_ 16 .S (.mk_uN 16384) (.mk_uN 16384) = .mk_uN 8192 := by decide
example : iq15mulr_sat_ 16 .S (.mk_uN 32768) (.mk_uN 32767) = .mk_uN 32769 := by decide
example : iq15mulr_sat_ 16 .S (.mk_uN 65535) (.mk_uN 16384) = .mk_uN 0 := by decide
example : inv_concat_ Nat [1, 2, 3, 4] = [[1, 2], [3, 4]] := by decide
example : inv_concat_ Nat [] = [] := by decide

end SpecExt.Builtins.Examples

-- The byte order differs from the bit-list order. These vectors include sign,
-- exponent and payload preservation, rather than only finite positive values.
example : ibytes_ 32 (.mk_uN 0x12345678) = [.mk_byte 0x78, .mk_byte 0x56, .mk_byte 0x34, .mk_byte 0x12] := by decide
example : inv_ibytes_ 32 [.mk_byte 0x78, .mk_byte 0x56, .mk_byte 0x34, .mk_byte 0x12] = .mk_uN 0x12345678 := by decide
example : fbytes_ 32 (.NEG (.SUBNORM 0)) = [.mk_byte 0, .mk_byte 0, .mk_byte 0, .mk_byte 128] := by decide
example : inv_fbytes_ 32 [.mk_byte 0, .mk_byte 0, .mk_byte 128, .mk_byte 63] = .POS (.NORM 0 0) := by decide
example : inv_fbytes_ 32 [.mk_byte 1, .mk_byte 0, .mk_byte 128, .mk_byte 127] = .POS (.NAN 1) := by decide
example : SpecExt.Builtins.floatBits 64 (.NEG (.NORM 0 0)) = 0xbff0000000000000 := by decide
example : SpecExt.Builtins.floatOfBits 64 0x7ff0000000000000 = .POS .INF := by decide
example : SpecExt.Builtins.floatOfBits 64 1 = .POS (.SUBNORM 1) := by decide
example : inv_nbytes_ .I32 (nbytes_ .I32 (.mk_num__0 .I32 (.mk_uN 0x12345678))) = .mk_num__0 .I32 (.mk_uN 0x12345678) := by decide
example : inv_vbytes_ .V128 (vbytes_ .V128 (.mk_uN 0x123456789abcdef0123456789abcdef0)) = .mk_uN 0x123456789abcdef0123456789abcdef0 := by decide

end
