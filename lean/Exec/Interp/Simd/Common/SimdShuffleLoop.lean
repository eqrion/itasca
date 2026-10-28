import Exec.Interp.Simd.Common.SimdShuffleSelect
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

def shuffleByte (op : U32) (bits x y : U128) (index : Nat) : BitVec 8 :=
  selectedByte (decide (op = 13#u32)) x.bv y.bv
    (laneBits 8 index (if op = 13#u32 then bits else y).bv).toNat

@[step] theorem shuffle_loop (op : U32) (bits x y initial : U128) (i : U32)
    (position : i.val ≤ 16)
    (initializedPrefix : ∀ j, j < i.val → laneBits 8 j initial.bv = shuffleByte op bits x y j) :
    runtime.interp.simd.shuffle_lanes_loop op bits x y initial i ⦃ result =>
      ∀ j, j < 16 → laneBits 8 j result.bv = shuffleByte op bits x y j ⦄ := by
  unfold runtime.interp.simd.shuffle_lanes_loop
  apply loop.spec_decr_nat (fun p => 16-p.2.val)
    (fun p => p.2.val ≤ 16 ∧ ∀ j, j < p.2.val → laneBits 8 j p.1.bv = shuffleByte op bits x y j)
  · rintro ⟨current,index⟩ ⟨indexBound,initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.shuffle_lanes_loop.body
    dsimp only
    split
    · rename_i more
      have less : index.val < 16 := by scalar_tac
      have choice : (if op = 13#u32 then Result.ok bits else Result.ok y) =
          Result.ok (if op = 13#u32 then bits else y) := by split <;> rfl
      rw [choice,bind_ok]
      step with lane as ⟨selector,selectorEq⟩
      have selectorBound : selector.val < 2^8 := by rw [selectorEq]; exact Nat.mod_lt _ (by decide)
      have selectorCast : (UScalar.cast .U32 selector).val =
          (laneBits 8 index.val (if op = 13#u32 then bits else y).bv).toNat := by
        rw [UScalar.cast_val_eq, Nat.mod_eq_of_lt (by scalar_tac)]
        rw [selectorEq,laneBits_toNat]
        rfl
      simp only [lift,bind_ok]
      step with shuffle_select as ⟨value,valueEq⟩
      rw [selectorCast] at valueEq
      have atIndex : value.bv.setWidth 8 = shuffleByte op bits x y index.val := valueEq
      step with put_lanes as ⟨updated,same,other⟩
      step as ⟨next,nextEq⟩
      refine ⟨?_,?_,?_⟩
      · omega
      · intro j bound
        by_cases eq : j = index.val
        · subst j; exact same.trans atIndex
        · exact (other j (by omega) eq).trans (initialized j (by omega))
      · omega
    · have finished : index.val = 16 := by scalar_tac
      simpa [finished] using initialized
  · exact ⟨position,initializedPrefix⟩

@[step] theorem shuffle_lanes (op : U32) (bits x y : U128) :
    runtime.interp.simd.shuffle_lanes op bits x y ⦃ result =>
      ∀ j, j < 16 → laneBits 8 j result.bv = shuffleByte op bits x y j ⦄ := by
  unfold runtime.interp.simd.shuffle_lanes
  exact shuffle_loop op bits x y 0#u128 0#u32 (by simp) (by simp)

end Itasca.Runtime.Interp.Simd
