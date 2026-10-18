import Exec.Interp.Relations.Range

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Scalar accesses use a mathematical 33-bit effective address. Both supported
machine-index widths agree on the exact endpoint test; failed checks trap. -/
def MemoryAddressEffect (address offset : U32) (width bytes : Usize)
    (result : core.result.Result Usize runtime.ExecError) : Prop :=
  if address.val + offset.val + width.val ≤ bytes.val then
    ∃ start, result = .Ok start ∧ start.val = address.val + offset.val
  else result = .Err (.Trap .MemoryOutOfBounds)

@[step] theorem memory_address_effect (address offset : U32) (width bytes : Usize) :
    runtime.interp.memory.address address offset width bytes
      ⦃ result => MemoryAddressEffect address offset width bytes result ⦄ := by
  have bytesCast := usize_to_u64_exact bytes
  have widthCast := usize_to_u64_exact width
  unfold runtime.interp.memory.address
  simp only [lift, bind_ok]
  step as ⟨start, hstart⟩
  split
  · rename_i outside
    simp only [core.convert.IntoFrom.into, runtime.ExecError.Insts.CoreConvertFromTrap,
      runtime.ExecError.Insts.CoreConvertFromTrap.from, bind_ok, WP.spec_ok, MemoryAddressEffect]
    split
    · scalar_tac
    · trivial
  · rename_i inside
    step as ⟨remaining, hremaining⟩
    split
    · rename_i outside
      simp only [core.convert.IntoFrom.into, runtime.ExecError.Insts.CoreConvertFromTrap,
        runtime.ExecError.Insts.CoreConvertFromTrap.from, bind_ok, WP.spec_ok, MemoryAddressEffect]
      split
      · scalar_tac
      · trivial
    · rename_i insideWidth
      have fits : address.val + offset.val + width.val ≤ bytes.val := by scalar_tac
      have startCast := cast_usize_exact start (by scalar_tac)
      simp [MemoryAddressEffect, fits, startCast]
      scalar_tac
end Exec.Interp
