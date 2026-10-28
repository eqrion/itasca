import Exec.Interp.Simd.Memory.SimdMemoryRange
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem full_store_unfold (offset lane : U32) (address value : U128) (memory : Slice U8) :
    runtime.interp.simd.memory_op 11#u32 offset lane address value memory = (do
      let result ← runtime.interp.memory.address (UScalar.cast .U32 address) offset 16#usize (Slice.len memory)
      match result with
      | .Err error => .ok (.Err error,memory)
      | .Ok start =>
        let updated ← runtime.interp.simd.write memory start 16#usize value
        .ok (.Ok 0#u128,updated)) := by
  unfold runtime.interp.simd.memory_op
  simp only [ite_true,lift,bind_ok]
  congr 1
  funext result
  cases result <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame, core.convert.FromSame.from, bind_ok]

def FullStoreEffect (offset : U32) (address value : U128) (memory : Slice U8)
    (out : core.result.Result U128 runtime.ExecError × Slice U8) : Prop :=
  if (UScalar.cast .U32 address).val + offset.val + 16 ≤ memory.length then
    out.1 = .Ok 0#u128 ∧ out.2.val = vectorStoreBytes memory.val
      ((UScalar.cast .U32 address).val + offset.val) value 0 16
  else out = (.Err (.Trap .MemoryOutOfBounds),memory)

@[step] theorem full_store_effect (offset lane : U32) (address value : U128) (memory : Slice U8) :
    runtime.interp.simd.memory_op 11#u32 offset lane address value memory
      ⦃ FullStoreEffect offset address value memory ⦄ := by
  rw [full_store_unfold]
  step with memory_range memory (UScalar.cast .U32 address) offset 16#usize (by decide) as ⟨result,effect⟩
  by_cases fits : (UScalar.cast .U32 address).val + offset.val + (16#usize).val ≤ memory.length
  · simp only [MemoryAddressEffect,Slice.len_val,fits,if_true] at effect
    obtain ⟨start,rfl,startEq⟩ := effect
    unfold runtime.interp.simd.write
    step with write_loop_effect value memory 16#usize start 0#usize (by decide)
      (by omega) (by simp) as ⟨updated,updatedEq⟩
    simpa [FullStoreEffect,fits,updatedEq,startEq]
  · simp only [MemoryAddressEffect,Slice.len_val,fits,if_false] at effect
    have outside : ¬ (UScalar.cast .U32 address).val + offset.val + 16 ≤ memory.length := by simpa using fits
    simp only [effect,WP.spec_ok,FullStoreEffect,if_neg outside]
end Itasca.Runtime.Interp.Simd
