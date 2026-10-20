import Exec.Spec.Wf
import SpecExt.Builtins.EncodingLemmas
import SpecExt.Builtins.Float.Decoding
import SpecExt.Builtins.Float.Storage
import Mathlib.Tactic

namespace Exec.Spec
open SpecExt.Builtins

private theorem byte_value_bound (value : byte) (hw : wf_byte value) : proj_byte_0 value < 256 := by
  cases value
  cases hw
  simp only [proj_byte_0]
  omega

/-- Well-formed little-endian bytes fit their represented width. -/
theorem integerOfBytes_bound (bytes : List byte) (valid : Forall wf_byte bytes) :
    integerOfBytes bytes < 256^bytes.length := by
  induction bytes with
  | nil => simp [integerOfBytes]
  | cons byte bytes ih =>
    have head := byte_value_bound byte (valid byte (by simp))
    have tail := ih (fun b member => valid b (by simp [member]))
    cases byte
    simp only [integerOfBytes, List.length_cons, Nat.pow_succ, proj_byte_0] at *
    omega

/-- Decoding and encoding an arbitrary well-formed byte string is exact,
including leading zero bytes. -/
theorem integerBytes_ofBytes (bytes : List byte) (valid : Forall wf_byte bytes) :
    integerBytes bytes.length (integerOfBytes bytes) = bytes := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
    have head := byte_value_bound byte (valid byte (by simp))
    have tail := ih (fun b member => valid b (by simp [member]))
    cases byte with | mk_byte bits =>
    simp only [integerOfBytes, List.length_cons, integerBytes, proj_byte_0] at *
    have low : (bits + 256 * integerOfBytes bytes) % 256 = bits := by omega
    have high : (bits + 256 * integerOfBytes bytes) / 256 = integerOfBytes bytes := by omega
    rw [low,high,tail]

def scalarNumBytes : numtype → Nat
  | .I32 | .F32 => 4
  | .I64 | .F64 => 8

/-- Fixed-width byte encoding is injective on its specified domain. The
domain bound is essential: encoding alone discards higher bits. -/
theorem integerBytes_injective (count left right : Nat)
    (leftBound : left < 256^count) (rightBound : right < 256^count)
    (same : integerBytes count left = integerBytes count right) : left = right := by
  have decoded := congrArg integerOfBytes same
  simpa only [integerBytes_roundtrip leftBound,integerBytes_roundtrip rightBound] using decoded

/-- Source-width guards make decoded integer load values unique for every
byte-aligned width, including packed and widening SIMD loads. -/
theorem ibytes_injective (bits : Nat) (aligned : bits % 8 = 0) (left right : uN)
    (leftBound : proj_uN_0 left < 2^bits) (rightBound : proj_uN_0 right < 2^bits)
    (same : ibytes_ bits left = ibytes_ bits right) : left = right := by
  have width : 256^(bits/8) = 2^bits := by
    calc
      256^(bits/8) = (2^8)^(bits/8) := by rfl
      _ = 2^(8*(bits/8)) := by rw [Nat.pow_mul]
      _ = 2^bits := by rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero aligned)]
  cases left with | mk_uN left =>
  cases right with | mk_uN right =>
  congr 1
  apply integerBytes_injective (bits/8) left right
  · simpa only [width,proj_uN_0] using leftBound
  · simpa only [width,proj_uN_0] using rightBound
  · exact same

/-- A successful read has one bounded decoded word even when the requested
slice is specified relationally. -/
theorem integer_read_value_unique (bits : Nat) (aligned : bits % 8 = 0)
    (payload : List byte) (left right : uN)
    (leftBound : proj_uN_0 left < 2^bits) (rightBound : proj_uN_0 right < 2^bits)
    (leftRead : ibytes_ bits left = payload) (rightRead : ibytes_ bits right = payload) :
    left = right :=
  ibytes_injective bits aligned left right leftBound rightBound (leftRead.trans rightRead.symm)

/-- Decoding a well-formed scalar encoding retains its complete value,
including signed zero and every floating-point NaN payload. -/
theorem numericBytes_decode (type : numtype) (value : num_) (typed : wf_num_ type value) :
    inv_nbytes_ type (nbytes_ type value) = value := by
  cases typed with
  | num__case_0 ty bits _ bounded same =>
    subst type
    cases bits with | mk_uN bits =>
    cases bounded with | uN_case_0 _ bound =>
    cases ty <;>
      simp only [numtype_Inn,nbytes_,inv_nbytes_,inv_ibytes_,ibytes_,proj_uN_0]
    all_goals
      congr 2
      apply integerBytes_roundtrip
      norm_num [size,valtype_Inn] at bound ⊢
      omega
  | num__case_1 ty value bounded same =>
    subst type
    cases ty
    · exact congrArg (num_.mk_num__1 .F32) (Float.fbytes_roundtrip_32 value bounded)
    · exact congrArg (num_.mk_num__1 .F64) (Float.fbytes_roundtrip_64 value bounded)

/-- Full scalar loads have a unique well-formed decoded result. -/
theorem numericBytes_injective (type : numtype) (left right : num_)
    (leftWf : wf_num_ type left) (rightWf : wf_num_ type right)
    (same : nbytes_ type left = nbytes_ type right) : left = right := by
  have decoded := congrArg (inv_nbytes_ type) same
  simpa only [numericBytes_decode type left leftWf,numericBytes_decode type right rightWf] using decoded

/-- The source numeric decoder and encoder are inverse for exactly sized byte
payloads, including every IEEE float bit pattern. -/
theorem numericBytes_roundtrip (ty : numtype) (bytes : List byte)
    (valid : Forall wf_byte bytes) (sized : bytes.length = scalarNumBytes ty) :
    nbytes_ ty (inv_nbytes_ ty bytes) = bytes := by
  have bounded := integerOfBytes_bound bytes valid
  have roundtrip := integerBytes_ofBytes bytes valid
  cases ty <;> simp only [scalarNumBytes] at sized
  · simpa [nbytes_,inv_nbytes_,ibytes_,inv_ibytes_,proj_uN_0,sized] using roundtrip
  · simpa [nbytes_,inv_nbytes_,ibytes_,inv_ibytes_,proj_uN_0,sized] using roundtrip
  · have bits : integerOfBytes bytes < 2^32 := by rw [sized] at bounded; norm_num at bounded ⊢; exact bounded
    simpa [nbytes_,inv_nbytes_,fbytes_,inv_fbytes_,Float.float_bits_roundtrip_32 _ bits,sized] using roundtrip
  · have bits : integerOfBytes bytes < 2^64 := by rw [sized] at bounded; norm_num at bounded ⊢; exact bounded
    simpa [nbytes_,inv_nbytes_,fbytes_,inv_fbytes_,Float.float_bits_roundtrip_64 _ bits,sized] using roundtrip
theorem numericBytes_wf (ty : numtype) (bytes : List byte)
    (valid : Forall wf_byte bytes) (sized : bytes.length = scalarNumBytes ty) :
    wf_num_ ty (inv_nbytes_ ty bytes) := by
  have bounded := integerOfBytes_bound bytes valid
  cases ty <;> simp only [scalarNumBytes] at sized
  · apply wf_num_.num__case_0 .I32 .I32 _ (by decide) _ rfl
    apply wf_uN.uN_case_0
    rw [sized] at bounded
    norm_num [size,valtype_Inn,inv_ibytes_,proj_uN_0] at bounded ⊢
    omega
  · apply wf_num_.num__case_0 .I64 .I64 _ (by decide) _ rfl
    apply wf_uN.uN_case_0
    rw [sized] at bounded
    norm_num [size,valtype_Inn,inv_ibytes_,proj_uN_0] at bounded ⊢
    omega
  · apply wf_num_.num__case_1 .F32 .F32 _ _ rfl
    apply Float.floatOfBits_wf_32
    rw [sized] at bounded
    simpa using bounded
  · apply wf_num_.num__case_1 .F64 .F64 _ _ rfl
    apply Float.floatOfBits_wf_64
    rw [sized] at bounded
    simpa using bounded
end Exec.Spec
