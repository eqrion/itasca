import Exec.Interp.Simd.Common.SimdExecutePure
import Exec.Interp.Relations.WordEncoding
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem vectorBits_toNat (words : List U64) (position : Nat) :
    (vectorBits words position).toNat =
      ((words[position]?).getD 0#u64).val + ((words[position+1]?).getD 0#u64).val * 2^64 := by
  let lo := (words[position]?).getD 0#u64
  let hi := (words[position+1]?).getD 0#u64
  have hlo : lo.val < 2^64 := by scalar_tac
  have hloWide : lo.val < 2^128 := by scalar_tac
  have hhiWide : hi.val < 2^128 := by scalar_tac
  have hshift : hi.val * 2^64 < 2^128 := by scalar_tac
  change (lo.bv.setWidth 128 ||| (hi.bv.setWidth 128 <<< 64)).toNat = lo.val + hi.val * 2^64
  simp only [BitVec.toNat_or,BitVec.toNat_shiftLeft,BitVec.toNat_setWidth,UScalar.bv_toNat]
  rw [Nat.mod_eq_of_lt hloWide,Nat.mod_eq_of_lt hhiWide,Nat.shiftLeft_eq,Nat.mod_eq_of_lt hshift]
  rw [Nat.or_comm,←Nat.shiftLeft_eq,←Nat.shiftLeft_add_eq_or_of_lt hlo,Nat.shiftLeft_eq]
  omega

theorem WordsAt.simd_vector {words : List U64} {position bits : Nat}
    (represented : WordsAt words position (Code.encodeValue (.VCONST .V128 (.mk_uN bits)))) :
    (simdInput words position 2#u32).val = bits := by
  change WordsAt words position [bits%2^64,bits/2^64] at represented
  obtain ⟨loBound,loValue⟩ := represented 0 (by simp)
  obtain ⟨hiBound,hiValue⟩ := represented 1 (by simp)
  simp only [Nat.add_zero,List.getElem!_cons_zero] at loBound loValue
  simp only [List.getElem!_cons_succ,List.getElem!_cons_zero] at hiValue
  change (vectorBits words position).toNat = bits
  rw [vectorBits_toNat]
  have lo : ((words[position]?).getD 0#u64).val = bits%2^64 := by
    simpa only [List.getElem?_eq_getElem loBound,Option.getD_some,_root_.getElem!_pos words position loBound] using loValue
  have hi : ((words[position+1]?).getD 0#u64).val = bits/2^64 := by
    simpa only [List.getElem?_eq_getElem hiBound,Option.getD_some,_root_.getElem!_pos words (position+1) hiBound] using hiValue
  rw [lo,hi,Nat.mul_comm]
  exact Nat.mod_add_div bits (2^64)

theorem ValuesAt.simd_vector_result {words : List U64} {base : Nat} {front : List val}
    (represented : ValuesAt words base front) (value : U128)
    (capacity : base + Code.slots (front.map Code.valueType) + 2 ≤ words.length) :
    ValuesAt (simdResultSlots words (base+Code.slots (front.map Code.valueType)) 2#u32 value) base
      (front ++ [.VCONST .V128 (.mk_uN value.val)]) := by
  have written := represented.append_vector (UScalar.cast .U64 value)
    ⟨(value.bv >>> 64).setWidth 64⟩ capacity
  have bits : (UScalar.cast .U64 value).val + ((value.bv >>> 64).setWidth 64).toNat * 2^64 = value.val := by
    simp only [UScalar.cast_val_eq,UScalarTy.numBits,BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,UScalar.bv_toNat]
    rw [Nat.shiftRight_eq_div_pow]
    have high : value.val / 2^64 < 2^64 := by scalar_tac
    rw [Nat.mod_eq_of_lt high,Nat.mul_comm]
    exact Nat.mod_add_div value.val (2^64)
  have decoded : Store.decodeWords .V128 (UScalar.cast .U64 value) ⟨(value.bv >>> 64).setWidth 64⟩ =
      .VCONST .V128 (.mk_uN value.val) := by
    change val.VCONST .V128 (.mk_uN ((UScalar.cast .U64 value).val + ((value.bv >>> 64).setWidth 64).toNat * 2^64)) = _
    rw [bits]
  simpa only [simdResultSlots,show (2#u32).val > 0 from by decide,↓reduceIte,decoded] using written

theorem WordsAt.simd_scalar {words : List U64} {position bits : Nat} (width : U32)
    (scalar : width ≠ 2#u32) (represented : WordsAt words position [bits]) :
    (simdInput words position width).val = bits := by
  obtain ⟨bound,value⟩ := represented 0 (by simp)
  simp only [Nat.add_zero,List.getElem!_cons_zero] at bound value
  have word : ((words[position]?).getD 0#u64).val = bits := by
    simpa only [List.getElem?_eq_getElem bound,Option.getD_some,_root_.getElem!_pos words position bound] using value
  simp only [simdInput,if_neg scalar,UScalar.cast_val_eq]
  rw [Nat.mod_eq_of_lt (by scalar_tac)]
  exact word

theorem ValuesAt.simd_scalar_result {words : List U64} {base : Nat} {front : List val}
    (represented : ValuesAt words base front) (ty : Itasca.types.ValueType) (value : U128)
    (scalar : ty ≠ .V128)
    (small : ty = .I32 ∨ ty = .F32 → (UScalar.cast .U64 value).val < 2^32)
    (capacity : base + Code.slots (front.map Code.valueType) < words.length) :
    ValuesAt (simdResultSlots words (base+Code.slots (front.map Code.valueType)) 1#u32 value) base
      (front ++ [Store.decodeWords ty (UScalar.cast .U64 value) 0#u64]) := by
  have written := represented.append_scalar ty (UScalar.cast .U64 value) 0#u64 scalar small capacity
  simpa only [simdResultSlots,show (1#u32).val > 0 from by decide,show (1#u32) ≠ 2#u32 from by decide,↓reduceIte] using written
end Exec.Interp
