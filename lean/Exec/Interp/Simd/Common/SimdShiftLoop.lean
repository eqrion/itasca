import Exec.Interp.Simd.Common.SimdShiftWord
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Exec.Spec.Simd

@[step] theorem shift_lanes_loop (kind : ShiftKind) (op width amount : U32) (x initial : U128) (i : U32)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64) (amountBound : amount.val < width.val)
    (operation : op.val%32=shiftCode kind) (position : i.val ≤ 128/width.val)
    (initializedPrefix : ∀ j, j < i.val → laneBits width.val j initial.bv = shiftBits kind (laneBits width.val j x.bv) amount.val) :
    runtime.interp.simd.shift_lanes_loop op x width amount initial i ⦃ result =>
      ∀ j, j < 128/width.val → laneBits width.val j result.bv = shiftBits kind (laneBits width.val j x.bv) amount.val ⦄ := by
  unfold runtime.interp.simd.shift_lanes_loop
  apply loop.spec_decr_nat (fun p => 128/width.val-p.2.val)
    (fun p => p.2.val ≤ 128/width.val ∧
      ∀ j, j < p.2.val → laneBits width.val j p.1.bv = shiftBits kind (laneBits width.val j x.bv) amount.val)
  · rintro ⟨current,index⟩ ⟨indexBound,initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.shift_lanes_loop.body
    step as ⟨count,countEq⟩
    split
    · rename_i more
      have less : index.val < 128/width.val := by scalar_tac
      have range := lane_range width.val index.val less
      step with lane_bits x width index positive widthBound (by omega) as ⟨value,input⟩
      step as ⟨selected,selectedEq⟩
      step with shift_word kind selected width amount value (laneBits width.val index.val x.bv) input
        positive widthBound amountBound (selectedEq.trans operation) as ⟨shifted,shiftedEq⟩
      step with put_lanes current width index shifted positive widthBound range as ⟨updated,same,other⟩
      have countBound : 128/width.val ≤ 128 := Nat.div_le_self _ _
      step as ⟨next,nextEq⟩
      refine ⟨?_,?_,?_⟩
      · omega
      · intro j bound
        by_cases eq : j=index.val
        · subst j; exact same.trans shiftedEq
        · rw [other j (lane_range _ _ (by omega)) eq]
          exact initialized j (by omega)
      · omega
    · have finished : index.val=128/width.val := by scalar_tac
      simpa [finished] using initialized
  · exact ⟨position,initializedPrefix⟩
end Exec.Interp.Simd
