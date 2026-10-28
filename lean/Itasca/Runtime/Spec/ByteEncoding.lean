import Itasca.Runtime.Spec.Wf
import SpecExt.Builtins.EncodingLemmas
import SpecExt.Builtins.Float.Decoding
import SpecExt.Builtins.Float.Storage
import Mathlib.Tactic

namespace Itasca.Runtime.Spec
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
end Itasca.Runtime.Spec
