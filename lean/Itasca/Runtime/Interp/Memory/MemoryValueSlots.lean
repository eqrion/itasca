import Itasca.Runtime.Interp.Memory.MemoryDescriptorValues
import Itasca.Runtime.Interp.Relations.Regions
namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt

theorem scalar_load_bytes_bound (bytes : List U8) (start width : Nat)
    (widthBound : width ≤ 8) (inside : start+width ≤ bytes.length) :
    (scalarLoadBytes bytes start 0#u64 0 width).val < 256^width := by
  rw [scalarLoadBytes_source bytes start width widthBound inside]
  have valid : Forall wf_byte (Store.decodeBytes ((bytes.drop start).take width)) := by
    intro b member
    obtain ⟨raw,_,rfl⟩ := List.mem_map.mp member
    constructor
    scalar_tac
  have lengthEq : (Store.decodeBytes ((bytes.drop start).take width)).length = width := by
    simp only [Store.decodeBytes,List.length_map,List.length_take,List.length_drop]
    omega
  simpa only [lengthEq] using Spec.integerOfBytes_bound _ valid

theorem load_word_small (op : Abs.Memory.Load) (word : U64)
    (bounded : word.val < 256^op.bytes) :
    op.type = .I32 ∨ op.type = .F32 → (scalarLoadedWord (loadOpcode op) word).val < 2^32 := by
  intro small
  cases op with
  | full ty =>
    cases ty <;> simp only [Abs.Memory.Load.type] at small
    · change word.val < 2^32
      exact bounded
    · simp at small
    · change word.val < 2^32
      exact bounded
    · simp at small
  | packed ty width sign =>
    cases ty with
    | I64 => simp [Abs.Memory.Load.type,numtype_Inn] at small
    | I32 =>
      cases width with
      | byte =>
        cases sign with
        | U => change word.val < 2^32; norm_num [Abs.Memory.Load.bytes,Abs.Memory.PackedWidth.bits] at bounded; omega
        | S =>
          change (UScalar.cast .U64 (IScalar.hcast .U32 (IScalar.cast .I32 (UScalar.hcast .I8 word)))).val < 2^32
          scalar_tac
      | half =>
        cases sign with
        | U => change word.val < 2^32; norm_num [Abs.Memory.Load.bytes,Abs.Memory.PackedWidth.bits] at bounded; omega
        | S =>
          change (UScalar.cast .U64 (IScalar.hcast .U32 (IScalar.cast .I32 (UScalar.hcast .I16 word)))).val < 2^32
          scalar_tac

theorem numeric_word_encode (ty : numtype) (word : U64)
    (small : ty = .I32 ∨ ty = .F32 → word.val < 2^32) :
    Code.encodeValue (Store.decodeWords (numericMemoryType ty) word 0#u64) = [word.val] := by
  cases ty
  · change [word.val % 2^32] = [word.val]
    rw [Nat.mod_eq_of_lt (small (Or.inl rfl))]
  · rfl
  · change [Builtins.floatBits 32 (Builtins.floatOfBits 32 (word.val % 2^32))] = [word.val]
    have bound := small (Or.inr rfl)
    rw [Nat.mod_eq_of_lt bound,Builtins.Float.float_bits_roundtrip_32 word.val bound]
  · change [Builtins.floatBits 64 (Builtins.floatOfBits 64 word.val)] = [word.val]
    rw [Builtins.Float.float_bits_roundtrip_64 word.val (by scalar_tac)]

theorem load_word_encode (op : Abs.Memory.Load) (bytes : List U8) (start : Nat)
    (inside : start + op.bytes ≤ bytes.length) :
    Code.encodeValue (op.value (Store.decodeBytes ((bytes.drop start).take op.bytes))) =
      [(scalarLoadedWord (loadOpcode op) (scalarLoadBytes bytes start 0#u64 0 op.bytes)).val] := by
  rw [←load_word_value op bytes start inside]
  apply numeric_word_encode
  apply load_word_small
  apply scalar_load_bytes_bound bytes start op.bytes
  · cases op with
    | full ty => cases ty <;> decide
    | packed ty width sign => cases width <;> simp [Abs.Memory.Load.bytes,Abs.Memory.PackedWidth.bits]
  · exact inside
end Itasca.Runtime.Interp.MemoryDescriptor
