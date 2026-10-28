import Itasca.Runtime.Interp.Memory.MemoryBytes

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

theorem scalarLoadWidth_bound (opcode : U16) : (scalarLoadWidth opcode).val ≤ 8 := by
  unfold scalarLoadWidth
  split <;> decide

theorem scalarStoreWidth_bound (opcode : U16) : (scalarStoreWidth opcode).val ≤ 8 := by
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
      (scalarLoadWidth_bound opcode) (by omega) (by simp) as ⟨word,wordEq⟩
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
      (scalarStoreWidth_bound opcode) (by omega) (by simp) as ⟨after,afterEq⟩
    simpa [ScalarStoreEffect,fits,afterEq,startEq]
  · simp only [MemoryAddressEffect, Slice.len_val, fits, if_false] at effect
    rw [effect]
    simp [ScalarStoreEffect,fits]
end Itasca.Runtime.Interp
