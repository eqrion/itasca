import Exec.Store.Api.Grow
import Exec.Representation.StoreInvariant
namespace Exec.Store
open Aeneas Aeneas.Std

def MemoryGrowRefusal {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (s : runtime.store.Store M) (m : runtime.store.MemInst M)
    (delta : U32) : Prop :=
  65536 < (view m.buf).length / 65536 + delta.val ∨
  (core.option.Option.unwrap_or m.maximum 65536#u32).val <
    (view m.buf).length / 65536 + delta.val ∨
  Usize.max < delta.val * 65536 ∨
  Usize.max < ((view m.buf).length / 65536 + delta.val) * 65536 ∨
  s.limits.max_memory_bytes.val < s.memory_bytes.val + delta.val * 65536 ∨
  ∃ requested : Usize, ∃ after : M,
    requested.val = ((view m.buf).length / 65536 + delta.val) * 65536 ∧
    ops.grow m.buf requested = .ok (false, after)

theorem memory_grow_refusal {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view)
    (s : runtime.store.Store M) (index : Usize) (delta : U32)
    (hindex : index.val < s.memories.length)
    (hsizes : ∀ m ∈ s.memories.val, (view m.buf).length ≤ 4294967296) :
    runtime.store.Store.grow_memory_index ops s index delta ⦃ result =>
      result.1 = core.num.U32.MAX → ∃ m,
        s.memories.val[index.val]? = some m ∧ MemoryGrowRefusal ops view s m delta ⦄ := by
  unfold runtime.store.Store.grow_memory_index
  step as ⟨m, hm⟩
  have hmem : m ∈ s.memories.val := by simp [hm]
  have hsize := hsizes m hmem
  have lookup : s.memories.val[index.val]? = some m := by simp [hm, hindex]
  rw [laws.read]
  simp [lift]
  step as ⟨old, hold⟩
  step as ⟨pages, hpages⟩
  split
  · simp only [WP.spec_ok]
    intro _
    exact ⟨m, lookup, Or.inl (by scalar_tac)⟩
  · split
    · simp only [WP.spec_ok]
      intro _
      exact ⟨m, lookup, Or.inr (Or.inl (by scalar_tac))⟩
    · step as ⟨add, hadd⟩
      split
      · simp only [WP.spec_ok]
        intro _
        exact ⟨m, lookup, Or.inr (Or.inr (Or.inl (by scalar_tac)))⟩
      · step as ⟨bytes, hbytes⟩
        split
        · simp only [WP.spec_ok]
          intro _
          exact ⟨m, lookup, Or.inr (Or.inr (Or.inr (Or.inl (by scalar_tac))))⟩
        · step with within_spec s.memory_bytes (UScalar.cast .Usize add) s.limits.max_memory_bytes as ⟨fits, hfits⟩
          split
          · step as ⟨m', back, hm', hback⟩
            have hsame : m' = m := by simp [hm, hm']
            have hcastPages : (UScalar.cast .Usize pages).val ≤ pages.val := by
              rw [UScalar.cast_val_eq]
              exact Nat.mod_le _ _
            step as ⟨newSize, hnewSize⟩
            obtain ⟨⟨grew, after⟩, actual, hafter⟩ := WP.spec_imp_exists (laws.grow m'.buf newSize)
            rw [actual]
            cases grew
            · simp
              refine ⟨m, lookup, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))⟩
              refine ⟨newSize, after, ?_, by simpa [hsame] using actual⟩
              have hpagesCast : (UScalar.cast .Usize pages).val = pages.val :=
                cast_usize_exact pages (by scalar_tac)
              simp only [hpagesCast] at hnewSize
              scalar_tac
            · simp
              step as ⟨count, hcount⟩
              intro returned
              have heq := congrArg (fun n : U32 => n.val) returned
              rw [UScalar.cast_val_eq] at heq
              change old.val % 4294967296 = 4294967295 at heq
              scalar_tac
          · simp only [WP.spec_ok]
            intro _
            refine ⟨m, lookup, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))⟩
            have hfail : ¬ s.memory_bytes.val + (UScalar.cast .Usize add).val ≤ s.limits.max_memory_bytes.val := by
              simpa [hfits] using ‹¬ fits = true›
            have castLe : (UScalar.cast .Usize add).val ≤ add.val := by
              rw [UScalar.cast_val_eq]
              exact Nat.mod_le _ _
            scalar_tac
end Exec.Store
