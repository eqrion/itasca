import Itasca.Runtime.Interp.Memory.MemoryAddress

/-!
Scalar memory byte encoding and handler effects. Exact little-endian byte calculations establish load/store widths, loaded words and the extracted scalar operation effects.
-/

/-! ## Memory Bytes -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

def scalarStoreByte (value : U64) (index : Nat) : U8 :=
  ⟨BitVec.ofNat 8 (value.val >>> (index * 8))⟩

def scalarStoreBytes (bytes : List U8) (start : Nat) (value : U64) (index : Nat) : Nat → List U8
  | 0 => bytes
  | count + 1 => scalarStoreBytes (bytes.set (start + index) (scalarStoreByte value index)) start value (index + 1) count

theorem scalar_store_bytes_length (bytes : List U8) (start : Nat) (value : U64) (index count : Nat) :
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

end

/-! ## Memory Scalar -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

def scalarLoadWidth (opcode : U16) : Usize :=
  match opcode with
  | 40#uscalar | 42#uscalar | 52#uscalar | 53#uscalar => 4#usize
  | 41#uscalar | 43#uscalar => 8#usize
  | 46#uscalar | 47#uscalar | 50#uscalar | 51#uscalar => 2#usize
  | _ => 1#usize

def scalarStoreWidth (opcode : U16) : Usize :=
  match opcode with
  | 54#uscalar | 56#uscalar | 62#uscalar => 4#usize
  | 55#uscalar | 57#uscalar => 8#usize
  | 59#uscalar | 61#uscalar => 2#usize
  | _ => 1#usize

def scalarLoadedWord (opcode : U16) (word : U64) : U64 :=
  match opcode with
  | 44#uscalar => UScalar.cast .U64 (IScalar.hcast .U32 (IScalar.cast .I32 (UScalar.hcast .I8 word)))
  | 46#uscalar => UScalar.cast .U64 (IScalar.hcast .U32 (IScalar.cast .I32 (UScalar.hcast .I16 word)))
  | 48#uscalar => IScalar.hcast .U64 (IScalar.cast .I64 (UScalar.hcast .I8 word))
  | 50#uscalar => IScalar.hcast .U64 (IScalar.cast .I64 (UScalar.hcast .I16 word))
  | 52#uscalar => IScalar.hcast .U64 (IScalar.cast .I64 (UScalar.hcast .I32 word))
  | _ => word

theorem scalar_load_width_bound (opcode : U16) : (scalarLoadWidth opcode).val ≤ 8 := by
  unfold scalarLoadWidth
  split <;> decide

theorem scalar_store_width_bound (opcode : U16) : (scalarStoreWidth opcode).val ≤ 8 := by
  unfold scalarStoreWidth
  split <;> decide

private theorem load_unfold (opcode : U16) (address offset : U32) (bytes : Slice U8) :
    runtime.interp.memory.load opcode address offset bytes = (do
      let result ← runtime.interp.memory.address address offset (scalarLoadWidth opcode) (Slice.len bytes)
      match result with
      | .Err error => .ok (.Err error)
      | .Ok start =>
        let word ← runtime.interp.memory.load_loop bytes (scalarLoadWidth opcode) start 0#u64 0#usize
        .ok (.Ok (scalarLoadedWord opcode word))) := by
  unfold runtime.interp.memory.load scalarLoadWidth
  split <;> simp only [bind_ok]
  all_goals
    congr 1
    funext result
    cases result <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, core.convert.FromSame.from, bind_ok]
  all_goals
    congr 1 <;> (funext word; simp [scalarLoadedWord, lift, bind_ok])
  all_goals split <;> simp_all [scalarLoadedWord, lift, bind_ok]

private theorem store_unfold (opcode : U16) (address offset : U32) (value : U64) (bytes : Slice U8) :
    runtime.interp.memory.store opcode address offset value bytes = (do
      let result ← runtime.interp.memory.address address offset (scalarStoreWidth opcode) (Slice.len bytes)
      match result with
      | .Err error => .ok (.Err error,bytes)
      | .Ok start =>
        let after ← runtime.interp.memory.store_loop value bytes (scalarStoreWidth opcode) start 0#usize
        .ok (.Ok (),after)) := by
  unfold runtime.interp.memory.store scalarStoreWidth
  split <;> simp only [bind_ok]
  all_goals
    congr 1
    funext result
    cases result <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, core.convert.FromSame.from, bind_ok]

def ScalarLoadEffect (opcode : U16) (address offset : U32) (bytes : Slice U8)
    (result : core.result.Result U64 runtime.ExecError) : Prop :=
  if address.val + offset.val + (scalarLoadWidth opcode).val ≤ bytes.length then
    result = .Ok (scalarLoadedWord opcode (scalarLoadBytes bytes.val (address.val + offset.val)
      0#u64 0 (scalarLoadWidth opcode).val))
  else result = .Err (.Trap .MemoryOutOfBounds)

def ScalarStoreEffect (opcode : U16) (address offset : U32) (value : U64) (bytes : Slice U8)
    (out : core.result.Result Unit runtime.ExecError × Slice U8) : Prop :=
  if address.val + offset.val + (scalarStoreWidth opcode).val ≤ bytes.length then
    out.1 = .Ok () ∧ out.2.val = scalarStoreBytes bytes.val (address.val + offset.val)
      value 0 (scalarStoreWidth opcode).val
  else out = (.Err (.Trap .MemoryOutOfBounds),bytes)

/-- Every scalar load either returns its exact little-endian value or the
specified bounds trap; the extracted computation itself never fails. -/
@[step] theorem memory_load_effect (opcode : U16) (address offset : U32) (bytes : Slice U8) :
    runtime.interp.memory.load opcode address offset bytes ⦃ ScalarLoadEffect opcode address offset bytes ⦄ := by
  rw [load_unfold]
  step with memory_address_effect address offset (scalarLoadWidth opcode) (Slice.len bytes) as ⟨result, effect⟩
  by_cases fits : address.val + offset.val + (scalarLoadWidth opcode).val ≤ bytes.length
  · simp only [MemoryAddressEffect, Slice.len_val, fits, if_true] at effect
    obtain ⟨start,rfl,startEq⟩ := effect
    step with memory_load_loop_effect bytes (scalarLoadWidth opcode) start 0#u64 0#usize
      (scalar_load_width_bound opcode) (by omega) (by simp) as ⟨word,wordEq⟩
    simpa [ScalarLoadEffect,fits,wordEq,startEq]
  · simp only [MemoryAddressEffect, Slice.len_val, fits, if_false] at effect
    rw [effect]
    simp [ScalarLoadEffect,fits]

/-- Scalar stores preserve the exact original buffer on a bounds trap. -/
@[step] theorem memory_store_effect (opcode : U16) (address offset : U32) (value : U64) (bytes : Slice U8) :
    runtime.interp.memory.store opcode address offset value bytes ⦃ ScalarStoreEffect opcode address offset value bytes ⦄ := by
  rw [store_unfold]
  step with memory_address_effect address offset (scalarStoreWidth opcode) (Slice.len bytes) as ⟨result, effect⟩
  by_cases fits : address.val + offset.val + (scalarStoreWidth opcode).val ≤ bytes.length
  · simp only [MemoryAddressEffect, Slice.len_val, fits, if_true] at effect
    obtain ⟨start,rfl,startEq⟩ := effect
    step with memory_store_loop_effect value bytes (scalarStoreWidth opcode) start 0#usize
      (scalar_store_width_bound opcode) (by omega) (by simp) as ⟨after,afterEq⟩
    simpa [ScalarStoreEffect,fits,afterEq,startEq]
  · simp only [MemoryAddressEffect, Slice.len_val, fits, if_false] at effect
    rw [effect]
    simp [ScalarStoreEffect,fits]
end Itasca.Runtime.Interp

end
