import Exec.Interp.State.TableMutation
import Exec.Store.Api.TableFillEffect
namespace Exec.Store
open Aeneas Aeneas.Std Exec.Interp

theorem fillTableWords_member (before : List U64) (start count : Nat) (value word : U64)
    (member : word ∈ fillTableWords before start value count) : word ∈ before ∨ word = value := by
  induction count with
  | zero => exact Or.inl member
  | succ count ih =>
    simp only [fillTableWords] at member
    rcases List.mem_or_eq_of_mem_set member with old | equal
    · exact ih old
    · exact Or.inr equal

theorem TableFillEffect.mutation {M : Type} (store : runtime.store.Store M)
    (address : runtime.TableAddr) (table : runtime.store.TableInst) (destination value count : U64)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M)
    (effect : TableFillEffect store address.index table destination value count out) :
    FrameStoreMetadata store out.2 ∧
    ((out.1 = .Ok () ∧ TableMutation store out.2 address table value) ∨
      (out.1 = .Err (.Trap .TableOutOfBounds) ∧ out.2 = store)) := by
  unfold TableFillEffect at effect
  split at effect
  · obtain ⟨words,rfl,filled⟩ := effect
    refine ⟨⟨rfl,rfl,rfl,rfl⟩,Or.inl ⟨rfl,words,rfl,?_,?_⟩⟩
    · simpa only [alloc.vec.Vec.length] using (congrArg List.length filled).trans (fillTableWords_length _ _ _ _)
    · intro word member
      rw [filled] at member
      exact fillTableWords_member _ _ _ _ _ member
  · rw [effect]
    exact ⟨⟨rfl,rfl,rfl,rfl⟩,Or.inr ⟨rfl,rfl⟩⟩
end Exec.Store
