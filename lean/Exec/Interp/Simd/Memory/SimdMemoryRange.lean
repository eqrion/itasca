import Exec.Interp.Simd.Memory.SimdMemoryBytes
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem memory_range (memory : Slice U8) (address offset : U32) (size : Usize)
    (small : size.val ≤ 16) :
    runtime.interp.simd.range memory address offset size
      ⦃ result => MemoryAddressEffect address offset size (Slice.len memory) result ⦄ := by
  have sizeCast := usize_to_u64_exact size
  have memoryCast := usize_to_u64_exact (Slice.len memory)
  unfold runtime.interp.simd.range
  simp only [lift,bind_ok]
  step as ⟨start,startEq⟩
  step as ⟨finish,finishEq⟩
  split
  · rename_i outside
    simp only [WP.spec_ok,MemoryAddressEffect]
    split
    · scalar_tac
    · trivial
  · rename_i inside
    have fits : address.val+offset.val+size.val ≤ (Slice.len memory).val := by scalar_tac
    have startCast := cast_usize_exact start (by scalar_tac)
    simp only [lift,bind_ok,WP.spec_ok,MemoryAddressEffect,if_pos fits]
    exact ⟨_,rfl,startCast.trans startEq⟩
end Exec.Interp.Simd
