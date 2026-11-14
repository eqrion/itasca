import Itasca.Runtime.Interp.Relations.Defaults
import Itasca.Runtime.Interp.Relations.Regions
import Itasca.Runtime.Interp.Memory.MemorySize
import Itasca.Runtime.Spec.FloatPromote
import Itasca.Runtime.Interp.Relations.SourceClosure

/-!
Sections, each formerly its own module: WordEncoding, PackedMemorySource, ReferenceSource.
-/

/-! ## WordEncoding -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt

/-- Canonical raw global words re-encode exactly, including reference zero and
both vector words. Only 32-bit numerical payloads need their canonical bound. -/
theorem encode_decode_words (ty : Itasca.wasm_types.ValueType) (lo hi : U64)
    (small : ty = .I32 ∨ ty = .F32 → lo.val < 2^32) :
    Compiler.encodeValue (Store.decodeWords ty lo hi) = pairWords ty (lo,hi) := by
  cases ty
  · change [lo.val % 2^32] = [lo.val]
    rw [Nat.mod_eq_of_lt (small (Or.inl rfl))]
  · rfl
  · change [Builtins.floatBits 32 (Builtins.floatOfBits 32 (lo.val % 2^32))] = [lo.val]
    have bound := small (Or.inr rfl)
    rw [Nat.mod_eq_of_lt bound,Builtins.Float.float_bits_roundtrip_32 lo.val bound]
  · change [Builtins.floatBits 64 (Builtins.floatOfBits 64 lo.val)] = [lo.val]
    rw [Builtins.Float.float_bits_roundtrip_64 lo.val (by scalar_tac)]
  · change [(lo.val+hi.val*2^64)%2^64,(lo.val+hi.val*2^64)/2^64] = [lo.val,hi.val]
    have bound : lo.val < 2^64 := by scalar_tac
    simp [Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt bound,Nat.add_mul_div_right,Nat.div_eq_of_lt bound]
    exact bound
  · by_cases zero : lo.val = 0
    · simp [Store.decodeWords,Store.decodeRef,zero,Store.refVal,Store.decodeElemType,Compiler.encodeValue,pairWords,sourceType]
    · have restore : lo.val - 1 + 1 = lo.val := by omega
      simp [Store.decodeWords,Store.decodeRef,zero,Store.refVal,Compiler.encodeValue,pairWords,sourceType,restore]
  · by_cases zero : lo.val = 0
    · simp [Store.decodeWords,Store.decodeRef,zero,Store.refVal,Store.decodeElemType,Compiler.encodeValue,pairWords,sourceType]
    · have restore : lo.val - 1 + 1 = lo.val := by omega
      simp [Store.decodeWords,Store.decodeRef,zero,Store.refVal,Compiler.encodeValue,pairWords,sourceType,restore]

theorem ValuesAt.append_scalar {words : List U64} {base : Nat} {front : List val}
    (represented : ValuesAt words base front) (ty : Itasca.wasm_types.ValueType) (lo hi : U64)
    (scalar : ty ≠ .V128) (small : ty = .I32 ∨ ty = .F32 → lo.val < 2^32)
    (capacity : base + Compiler.slots (front.map Compiler.valueType) < words.length) :
    ValuesAt (words.set (base + Compiler.slots (front.map Compiler.valueType)) lo) base
      (front ++ [Store.decodeWords ty lo hi]) := by
  have same : pairWords ty (lo,hi) = [lo.val] := by cases ty <;> simp_all [pairWords,sourceType]
  have written := WordsAt.set_append represented lo (by simpa only [Compiler.encode_values_length] using capacity)
  change WordsAt _ _ (Compiler.encodeValues (front ++ [Store.decodeWords ty lo hi]))
  rw [Compiler.encode_values_append]
  rw [show Compiler.encodeValues [Store.decodeWords ty lo hi] = Compiler.encodeValue (Store.decodeWords ty lo hi) by simp [Compiler.encodeValues]]
  rw [encode_decode_words ty lo hi small,same]
  simpa only [Compiler.encode_values_length] using written

theorem ValuesAt.append_vector {words : List U64} {base : Nat} {front : List val}
    (represented : ValuesAt words base front) (lo hi : U64)
    (capacity : base + Compiler.slots (front.map Compiler.valueType) + 2 ≤ words.length) :
    ValuesAt ((words.set (base + Compiler.slots (front.map Compiler.valueType)) lo).set
      (base + Compiler.slots (front.map Compiler.valueType)+1) hi) base
      (front ++ [Store.decodeWords .V128 lo hi]) := by
  have first := WordsAt.set_append represented lo (by rw [Compiler.encode_values_length]; omega)
  have second := first.set_append hi (by simp only [List.length_append,List.length_cons,List.length_nil,
    List.length_set,Compiler.encode_values_length]; omega)
  change WordsAt _ _ (Compiler.encodeValues (front ++ [Store.decodeWords .V128 lo hi]))
  rw [Compiler.encode_values_append]
  rw [show Compiler.encodeValues [Store.decodeWords .V128 lo hi] = Compiler.encodeValue (Store.decodeWords .V128 lo hi) by simp [Compiler.encodeValues]]
  rw [encode_decode_words .V128 lo hi (by simp)]
  change WordsAt _ _ (Compiler.encodeValues front ++ [lo.val,hi.val])
  simpa only [Compiler.encode_values_length,List.length_append,List.length_cons,List.length_nil,
    List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.zero_add] using second

end Itasca.Runtime.Interp

end

/-! ## PackedMemorySource -/

section

/-!
Packed memory descriptors and source decoding. Width, stored-byte and signed-word facts establish the decoded load value used by packed-memory correspondence.
-/

/-! ## Packed Memory -/

section

namespace Itasca.Runtime.Interp.PackedMemory
open Aeneas Aeneas.Std SpecExt

def loadOpcode (op : Spec.PackedMemory) (sign : sx) : U16 :=
  match op,sign with
  | .i32x8,.S => 44#u16
  | .i32x8,.U => 45#u16
  | .i32x16,.S => 46#u16
  | .i32x16,.U => 47#u16
  | .i64x8,.S => 48#u16
  | .i64x8,.U => 49#u16
  | .i64x16,.S => 50#u16
  | .i64x16,.U => 51#u16
  | .i64x32,.S => 52#u16
  | .i64x32,.U => 53#u16

def storeOpcode : Spec.PackedMemory → U16
  | .i32x8 => 58#u16
  | .i32x16 => 59#u16
  | .i64x8 => 60#u16
  | .i64x16 => 61#u16
  | .i64x32 => 62#u16

theorem load_width (op : Spec.PackedMemory) (sign : sx) :
    (scalarLoadWidth (loadOpcode op sign)).val = op.bytes := by cases op <;> cases sign <;> rfl

theorem store_width (op : Spec.PackedMemory) :
    (scalarStoreWidth (storeOpcode op)).val = op.bytes := by cases op <;> rfl

def storeBits (op : Spec.PackedMemory) (word : U64) : Nat :=
  match op.type with | .I32 => word.val % 2^32 | .I64 => word.val

theorem store_bytes (op : Spec.PackedMemory) (word : U64) :
    op.stored (storeBits op word) =
      Builtins.integerBytes op.bytes word.val := by
  cases op
  · change Builtins.integerBytes 1 (word.val % 2^32) = Builtins.integerBytes 1 word.val
    simp only [Builtins.integerBytes,Nat.mod_mod_of_dvd _ (by norm_num : 256 ∣ 2^32)]
  · change Builtins.integerBytes 2 (word.val % 2^32) = _
    have low := Spec.integer_bytes_mod 2 (word.val % 2^32)
    have raw := Spec.integer_bytes_mod 2 word.val
    rw [Nat.mod_mod_of_dvd _ (by norm_num : 256^2 ∣ 2^32)] at low
    exact low.symm.trans raw
  · rfl
  · rfl
  · rfl

def signedWord (op : Spec.PackedMemory) (word : U64) : U64 :=
  match op with
  | .i32x8 => UScalar.cast .U64 (IScalar.hcast .U32 (IScalar.cast .I32 (UScalar.hcast .I8 word)))
  | .i32x16 => UScalar.cast .U64 (IScalar.hcast .U32 (IScalar.cast .I32 (UScalar.hcast .I16 word)))
  | .i64x8 => IScalar.hcast .U64 (IScalar.cast .I64 (UScalar.hcast .I8 word))
  | .i64x16 => IScalar.hcast .U64 (IScalar.cast .I64 (UScalar.hcast .I16 word))
  | .i64x32 => IScalar.hcast .U64 (IScalar.cast .I64 (UScalar.hcast .I32 word))

theorem load_word_value (op : Spec.PackedMemory) (sign : sx) (word : U64)
    (bounded : word.val < 2^op.bits) :
    Store.decodeWords (numericMemoryType (numtype_Inn op.type)) (scalarLoadedWord (loadOpcode op sign) word) 0#u64 =
      .CONST (numtype_Inn op.type) (.mk_num__0 op.type
        (extend__ op.bits (sizenn (numtype_Inn op.type)) sign (.mk_uN word.val))) := by
  cases sign
  · have unsigned : scalarLoadedWord (loadOpcode op .U) word = word := by cases op <;> rfl
    rw [unsigned]
    cases op <;> simp only [Spec.PackedMemory.type,numericMemoryType,numtype_Inn,Store.decodeWords,extend__]
    all_goals rw [Nat.mod_eq_of_lt (by simp only [Spec.PackedMemory.bits] at bounded; omega)]
  · have inputEq : (word.bv.setWidth op.bits).toNat = word.val := by
      rw [BitVec.toNat_setWidth,UScalar.bv_toNat,Nat.mod_eq_of_lt bounded]
    have extension := Spec.extend_signed_bitvec op.bits (sizenn (numtype_Inn op.type)) (word.bv.setWidth op.bits)
    rw [inputEq] at extension
    have signed : scalarLoadedWord (loadOpcode op .S) word = signedWord op word := by cases op <;> rfl
    rw [extension,signed]
    cases op <;> simp only [Spec.PackedMemory.type,Spec.PackedMemory.bits,signedWord,
      numtype_Inn,numericMemoryType,Store.decodeWords,sizenn,size,valtype_numtype,Option.get!_some]
    all_goals try rw [U32.cast_U64_val_eq]
    all_goals
      simp only [←UScalar.bv_toNat,IScalar.hcast_bv_eq,IScalar.cast_bv_eq,UScalar.hcast_bv_eq,
        IScalarTy.numBits,UScalarTy.numBits,BitVec.signExtend_eq]
    all_goals congr 3
    all_goals exact Nat.mod_eq_of_lt (BitVec.isLt _)
end Itasca.Runtime.Interp.PackedMemory

end

/-! ## Packed Memory Source -/

section

namespace Itasca.Runtime.Interp.PackedMemory
open Aeneas Aeneas.Std SpecExt

private theorem machine_bytes_wf (bytes : List U8) : Forall wf_byte (Store.decodeBytes bytes) := by
  intro byte member
  obtain ⟨raw,_,rfl⟩ := List.mem_map.mp member
  constructor
  scalar_tac

theorem load_word_decodes (op : Spec.PackedMemory) (sign : sx) (bytes : List U8) (start : Nat)
    (inside : start + op.bytes ≤ bytes.length) :
    Store.decodeWords (numericMemoryType (numtype_Inn op.type))
      (scalarLoadedWord (loadOpcode op sign) (scalarLoadBytes bytes start 0#u64 0 op.bytes)) 0#u64 =
      .CONST (numtype_Inn op.type) (op.loaded sign (Store.decodeBytes ((bytes.drop start).take op.bytes))) := by
  have width : op.bytes ≤ 8 := by cases op <;> decide
  have wordEq := scalar_load_bytes_source bytes start op.bytes width inside
  have payloadWf := machine_bytes_wf ((bytes.drop start).take op.bytes)
  have payloadLength : (Store.decodeBytes ((bytes.drop start).take op.bytes)).length = op.bytes := by
    simp only [Store.decodeBytes,List.length_map,List.length_take,List.length_drop]
    omega
  have bounded := Spec.integer_of_bytes_bound _ payloadWf
  rw [payloadLength] at bounded
  have power : 256^op.bytes = 2^op.bits := by cases op <;> decide
  rw [power] at bounded
  rw [load_word_value op sign _ (by rw [wordEq]; exact bounded)]
  simp only [Spec.PackedMemory.loaded,inv_ibytes_,wordEq]

end Itasca.Runtime.Interp.PackedMemory

end

end

/-! ## ReferenceSource -/

section

/-!
Reference-null execution and source encoding. The null-test result and encode/decode facts connect concrete reference words to source reference values.
-/

/-! ## Reference Null -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- The reference test compares the complete encoded word with the null
sentinel and writes exactly the canonical i32 Boolean. -/
@[step] theorem ref_is_null_effect
    (exec : runtime.interp.Execution) (base : Usize) (dst src : U32)
    (sourceBound : base.val+src.val < exec.slots.length)
    (destinationBound : base.val+dst.val < exec.slots.length) :
    runtime.interp.execute_ref_is_null exec base dst src ⦃ out =>
      out.1 = .Ok () ∧ SlotsEffect exec out.2
        (exec.slots.val.set (base.val+dst.val)
          (if exec.slots.val[base.val+src.val]! = 0#u64 then 1#u64 else 0#u64)) ⦄ := by
  unfold runtime.interp.execute_ref_is_null
  simp only [lift,bind_ok]
  step as ⟨position,positionEq⟩
  have positionVal : position.val = base.val+src.val := by simpa only [U32.cast_Usize_val_eq] using positionEq
  have found : exec.slots.val[position.val]? = some exec.slots.val[base.val+src.val]! := by
    rw [positionVal,getElem!_pos exec.slots.val _ sourceBound]
    exact List.getElem?_eq_getElem sourceBound
  step with vec_index_given exec.slots position exec.slots.val[base.val+src.val]! found as ⟨word,wordEq⟩
  simp only [wordEq]
  split <;> step* <;> simp_all [SlotsEffect,_root_.getElem!_pos]

end Itasca.Runtime.Interp

end

/-! ## Reference Source -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store

/-- The complete raw reference word uses exactly zero for either null type. -/
theorem decode_ref_is_null (ty : Itasca.wasm_types.ElemType) (word : U64) :
    Spec.referenceIsNull (decodeRef ty word) = if word = 0#u64 then 1 else 0 := by
  have zero : word = 0#u64 ↔ word.val = 0 := by scalar_tac
  by_cases null : word.val = 0 <;> cases ty <;> simp [decodeRef,decodeElemType,Spec.referenceIsNull,zero,null]

/-- Every raw reference, including the largest encoded address, re-encodes
without loss. Address validity is a separate store invariant. -/
theorem encode_decoded_ref (ty : Itasca.wasm_types.ElemType) (word : U64) :
    Compiler.encodeValue (refVal (decodeRef ty word)) = [word.val] := by
  cases ty
  · simpa only [decodeWords,pairWords,sourceType,reduceCtorEq,ite_false] using encode_decode_words .FuncRef word 0#u64 (by simp)
  · simpa only [decodeWords,pairWords,sourceType,reduceCtorEq,ite_false] using encode_decode_words .ExternRef word 0#u64 (by simp)

end Itasca.Runtime.Interp

end

end
