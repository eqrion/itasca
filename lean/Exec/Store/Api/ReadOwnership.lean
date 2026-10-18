import Exec.Store.Invariant.ValueRead
import Exec.Store.Api.Write

namespace Exec.Store
open Aeneas Aeneas.Std

/-- Values read from canonical globals satisfy the same owned-value invariant
required by subsequent definition, write, growth, and invocation APIs. -/
theorem global_read_owned {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (s : runtime.store.Store M) (hs : Shape view s)
    (index : Usize) (hindex : index.val < s.globals.length) :
    runtime.store.Store.global ops s ⟨s.id, index⟩ ⦃ answer =>
      ∃ value, answer = .Ok value ∧ ValueInStore s value ⦄ := by
  unfold runtime.store.Store.global
  simp [runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch]
  step as ⟨global, hglobal⟩
  have hcanonical := hs.globals global (by simp [hglobal])
  step with decode_global_owned s global hcanonical as ⟨value, hvalue⟩
  exact ⟨value, rfl, hvalue⟩

/-- Table reads are total for every element index and return only references
owned by this store; an invalid index returns the specified bounds trap. -/
theorem table_read_owned {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (s : runtime.store.Store M) (hs : Shape view s)
    (tableIndex : Usize) (index : U32) (htable : tableIndex.val < s.tables.length) :
    runtime.store.Store.table_get ops s ⟨s.id, tableIndex⟩ index ⦃ answer =>
      answer = .Err (.Trap .TableOutOfBounds) ∨
        ∃ value, answer = .Ok value ∧ ValueInStore s value ⦄ := by
  unfold runtime.store.Store.table_get
  simp [runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch]
  step as ⟨table, htableEq⟩
  simp [lift]
  split
  · simp
  · step as ⟨word, hword⟩
    have href := (hs.tables table (by simp [htableEq])).2.2 word (by simp [hword])
    let global : runtime.store.GlobalInstance :=
      {ty := {mutability := .Const, valtype := elementValueType table.ty}, lo := word, hi := 0#u64}
    have hglobal : GlobalShape s global := by
      cases ht : table.ty <;> simpa [GlobalShape, global, elementValueType, ht] using href
    step with decode_global_owned s global hglobal as ⟨value, hvalue⟩
    exact Or.inr ⟨value, rfl, hvalue⟩

end Exec.Store
