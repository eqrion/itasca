import Exec.Store.Api.Grow
import Exec.Representation.StoreInvariant
namespace Exec.Store
open Aeneas Aeneas.Std

/-- A concrete failed table-growth decision retains either a source ceiling,
a store-wide budget violation, or the actual allocator refusal. -/
def TableGrowRefusal {M A : Type} (allocator : runtime.platform.Alloc A)
    (s : runtime.store.Store M) (table : runtime.store.TableInst) (delta : U32) : Prop :=
  U32.max < table.elements.length + delta.val ∨
  (core.option.Option.unwrap_or table.maximum core.num.U32.MAX).val < table.elements.length + delta.val ∨
  s.limits.max_table_elements.val < s.table_elements.val + delta.val ∨
  allocator.reserve table.elements (UScalar.cast .Usize delta) = .ok (false, table.elements)

theorem table_grow_refusal {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (s : runtime.store.Store M) (index : Usize) (delta : U32) (value : U64)
    (hindex : index.val < s.tables.length)
    (hsizes : ∀ t ∈ s.tables.val, t.elements.length ≤ U32.max) :
    runtime.store.Store.grow_table_index ops allocator s index delta value ⦃ result =>
      result.1 = core.num.U32.MAX → ∃ table,
        s.tables.val[index.val]? = some table ∧
        (TableGrowRefusal allocator s table delta ∨
          (table.elements.length = U32.max ∧ delta.val = 0)) ⦄ := by
  unfold runtime.store.Store.grow_table_index
  step as ⟨t, ht⟩
  have htable : t ∈ s.tables.val := by simp [ht]
  have hsize := by simpa only [U32.max_eq] using hsizes t htable
  have lookup : s.tables.val[index.val]? = some t := by simp [ht, hindex]
  simp [lift]
  step as ⟨n, hn⟩
  have castOld : (UScalar.cast .U64 (alloc.vec.Vec.len t.elements)).val = t.elements.length := by
    rw [UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    change t.elements.length < 18446744073709551616
    have bound : t.elements.length ≤ 4294967295 := by simpa only [U32.max_eq] using hsize
    omega
  have nEq : n.val = t.elements.length + delta.val := by
    simpa only [castOld, U32.cast_U64_val_eq] using hn
  split
  · simp only [WP.spec_ok]
    intro _
    refine ⟨t, lookup, Or.inl (Or.inl ?_)⟩
    rw [U32.max_eq]
    have h : 4294967295 < n.val := by simpa only [U32.rMax] using ‹U32.rMax < n.val›
    omega
  · split
    · simp only [WP.spec_ok]
      intro _
      exact ⟨t, lookup, Or.inl (Or.inr (Or.inl (by scalar_tac)))⟩
    · step with within_spec s.table_elements (UScalar.cast .Usize delta) s.limits.max_table_elements as ⟨fits, hfits⟩
      split
      · step as ⟨t', back, ht', hback⟩
        have hsame : t' = t := by simp [ht, ht']
        obtain ⟨answer, hreserve⟩ := ha.reserve_eq t'.elements (UScalar.cast .Usize delta)
        rw [hreserve]
        cases answer
        · simp
          exact ⟨t, lookup, Or.inl (Or.inr (Or.inr (Or.inr (by simpa [hsame] using hreserve))))⟩
        · simp
          step with table_grow_loop t'.elements n (alloc.vec.Vec.len t.elements) value
            (by simp [hsame]) (by simp [hsame]; scalar_tac) (by scalar_tac) as ⟨elements, helements⟩
          step as ⟨count, hcount⟩
          intro returned
          refine ⟨t, lookup, Or.inr ?_⟩
          have returnedVal := congrArg (fun x : U32 => x.val) returned
          rw [UScalar.cast_val_eq] at returnedVal
          change t.elements.length % 4294967296 = 4294967295 at returnedVal
          have bound : t.elements.length ≤ 4294967295 := by simpa only [U32.max_eq] using hsize
          rw [Nat.mod_eq_of_lt (by omega)] at returnedVal
          rw [U32.max_eq]
          scalar_tac
      · simp only [WP.spec_ok]
        intro _
        refine ⟨t, lookup, Or.inl (Or.inr (Or.inr (Or.inl ?_)))⟩
        have hfail : ¬ s.table_elements.val + (UScalar.cast .Usize delta).val ≤ s.limits.max_table_elements.val := by
          simpa [hfits] using ‹¬ fits = true›
        have castLe : (UScalar.cast .Usize delta).val ≤ delta.val := by
          rw [UScalar.cast_val_eq]
          exact Nat.mod_le _ _
        omega
end Exec.Store
