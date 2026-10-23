import Exec.Interp.Memory.MemoryDispatch
import Exec.Interp.Memory.MemoryDecode
import Exec.Spec.PackedMemory

namespace Exec.Interp.PackedMemory
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
    have low := Spec.integerBytes_mod 2 (word.val % 2^32)
    have raw := Spec.integerBytes_mod 2 word.val
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
end Exec.Interp.PackedMemory
