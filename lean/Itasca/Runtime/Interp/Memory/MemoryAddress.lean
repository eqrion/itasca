import Itasca.Runtime.Interp.Relations.Range

namespace Itasca.Runtime.Interp
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
  have widthCast := usize_to_u64_exact width
  unfold runtime.interp.memory.address
  simp only [lift, bind_ok]
  step as ⟨start, hstart⟩
  step with range_effect start (UScalar.cast .U64 width) bytes .MemoryOutOfBounds as ⟨r, hr⟩
  simp only [RangeEffect] at hr
  split at hr
  · rename_i fits
    obtain ⟨range, rfl, hstartEq, _⟩ := hr
    have inside : address.val + offset.val + width.val ≤ bytes.val := by scalar_tac
    simp [core.result.Result.Insts.CoreOpsTry.branch, MemoryAddressEffect, inside]
    scalar_tac
  · rename_i outside
    subst hr
    have notInside : ¬ address.val + offset.val + width.val ≤ bytes.val := by scalar_tac
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, MemoryAddressEffect, notInside]
end Itasca.Runtime.Interp
