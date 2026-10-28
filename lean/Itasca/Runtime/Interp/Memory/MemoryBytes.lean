import Itasca.Runtime.Interp.Memory.MemoryAddress

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

def scalarStoreByte (value : U64) (index : Nat) : U8 :=
  ⟨BitVec.ofNat 8 (value.val >>> (index * 8))⟩

def scalarStoreBytes (bytes : List U8) (start : Nat) (value : U64) (index : Nat) : Nat → List U8
  | 0 => bytes
  | count + 1 => scalarStoreBytes (bytes.set (start + index) (scalarStoreByte value index)) start value (index + 1) count

theorem scalarStoreBytes_length (bytes : List U8) (start : Nat) (value : U64) (index count : Nat) :
    (scalarStoreBytes bytes start value index count).length = bytes.length := by
  induction count generalizing bytes index with
  | zero => rfl
  | succ count ih => simp only [scalarStoreBytes, ih, List.length_set]

/-- The complete extracted store loop terminates and writes precisely the
selected little-endian bytes, without changing the buffer length. -/
@[step] theorem memory_store_loop_effect (value : U64) (bytes : Slice U8) (width start index : Usize)
    (small : width.val ≤ 8) (inside : start.val + width.val ≤ bytes.length) (initial : index.val ≤ width.val) :
    runtime.interp.memory.store_loop value bytes width start index ⦃ out =>
      out.val = scalarStoreBytes bytes.val start.val value index.val (width.val - index.val) ⦄ := by
  unfold runtime.interp.memory.store_loop
  apply loop.spec_decr_nat (fun p => width.val - p.2.val)
    (fun p => p.2.val ≤ width.val ∧ p.1.length = bytes.length ∧
      scalarStoreBytes p.1.val start.val value p.2.val (width.val - p.2.val) =
        scalarStoreBytes bytes.val start.val value index.val (width.val - index.val))
  · rintro ⟨current, position⟩ ⟨bound, lengthEq, effect⟩
    dsimp only at bound lengthEq effect
    unfold runtime.interp.memory.store_loop.body
    dsimp only
    split
    · rename_i more
      have positionBound : position.val < width.val := by scalar_tac
      step as ⟨shift, shiftEq⟩
      step as ⟨shifted, shiftedEq, shiftedBits⟩
      step as ⟨destination, destinationEq⟩
      step as ⟨byte, byteCast⟩
      step as ⟨updated, updatedEq⟩
      step as ⟨next, nextEq⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · scalar_tac
      · simpa [updatedEq] using lengthEq
      · have remaining : width.val - position.val = (width.val - next.val) + 1 := by omega
        rw [remaining, scalarStoreBytes] at effect
        have byteEq : UScalar.cast .U8 shifted = scalarStoreByte value position.val := by
          apply UScalar.eq_of_val_eq
          change (UScalar.cast .U8 shifted).val = (value.val >>> (position.val * 8)) % 256
          rw [UScalar.cast_val_eq, shiftedEq, shiftEq]
          rfl
        simpa only [updatedEq, Slice.set_val_eq, destinationEq, nextEq, byteCast, byteEq] using effect
      · omega
    · have finished : position.val = width.val := by scalar_tac
      simpa [finished, scalarStoreBytes] using effect
  · exact ⟨initial, rfl, rfl⟩
/-- Little-endian accumulation in the machine word, with explicit byte position. -/
def scalarLoadByte (value : U64) (byte : U8) (index : Nat) : U64 :=
  value ||| (⟨(UScalar.cast .U64 byte).bv <<< (index * 8)⟩ : U64)

def scalarLoadBytes (bytes : List U8) (start : Nat) (value : U64) (index : Nat) : Nat → U64
  | 0 => value
  | count + 1 => scalarLoadBytes bytes start
      (scalarLoadByte value bytes[start + index]! index) (index + 1) count

/-- The extracted load loop terminates and accumulates exactly the requested
bytes, preserving their little-endian order. -/
@[step] theorem memory_load_loop_effect (bytes : Slice U8) (width start : Usize) (value : U64) (index : Usize)
    (small : width.val ≤ 8) (inside : start.val + width.val ≤ bytes.length) (initial : index.val ≤ width.val) :
    runtime.interp.memory.load_loop bytes width start value index ⦃ out =>
      out = scalarLoadBytes bytes.val start.val value index.val (width.val - index.val) ⦄ := by
  unfold runtime.interp.memory.load_loop
  apply loop.spec_decr_nat (fun p => width.val - p.2.val)
    (fun p => p.2.val ≤ width.val ∧
      scalarLoadBytes bytes.val start.val p.1 p.2.val (width.val - p.2.val) =
        scalarLoadBytes bytes.val start.val value index.val (width.val - index.val))
  · rintro ⟨current, position⟩ ⟨bound, effect⟩
    dsimp only at bound effect
    unfold runtime.interp.memory.load_loop.body
    dsimp only
    split
    · rename_i more
      have positionBound : position.val < width.val := by scalar_tac
      step as ⟨source, sourceEq⟩
      step as ⟨byte, byteEq⟩
      step as ⟨wide, wideEq⟩
      step as ⟨shift, shiftEq⟩
      step as ⟨shifted, shiftedEq, shiftedBits⟩
      step as ⟨updated, updatedEq, updatedBits⟩
      step as ⟨next, nextEq⟩
      refine ⟨?_, ?_, ?_⟩
      · scalar_tac
      · have remaining : width.val - position.val = (width.val - next.val) + 1 := by omega
        rw [remaining, scalarLoadBytes] at effect
        have read : byte = bytes.val[start.val + position.val]! := by
          have bound : start.val + position.val < bytes.val.length := by change start.val + position.val < bytes.length; omega
          rw [getElem!_pos bytes.val _ bound]
          simpa only [sourceEq] using byteEq
        have update : updated = scalarLoadByte current bytes.val[start.val + position.val]! position.val := by
          apply U64.bv_eq_imp_eq
          rw [updatedBits, shiftedBits, wideEq, read, shiftEq]
          rfl
        simpa only [update, nextEq] using effect
      · omega
    · have finished : position.val = width.val := by scalar_tac
      simpa [finished, scalarLoadBytes] using effect
  · exact ⟨initial, rfl⟩
end Itasca.Runtime.Interp
