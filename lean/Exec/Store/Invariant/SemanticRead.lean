import Exec.Store.Invariant.ValueRead
import Exec.Store.Api.Read
import Exec.Store.Api.Write

namespace Exec.Store
open Aeneas Aeneas.Std

/-- Reading an issued global handle returns exactly the value of the decoded
specification global, including the complete float bit pattern. -/
theorem global_read_boundary {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (s : runtime.store.Store M) (hs : Shape view s)
    (index : Usize) (hindex : index.val < s.globals.length) :
    runtime.store.Store.global ops s ⟨s.id, index⟩ ⦃ answer =>
      ∃ value, answer = .Ok value ∧
        Interp.rawType value = (s.globals.val[index.val]).ty.valtype ∧
        Interp.sourceValue value = (decodeGlobal (s.globals.val[index.val])).VALUE ⦄ := by
  unfold runtime.store.Store.global
  simp [runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch]
  step as ⟨global, hglobal⟩
  have hcanonical := hs.globals global (by simp [hglobal])
  have href : global.ty.valtype = .FuncRef ∨ global.ty.valtype = .ExternRef → global.lo.val ≤ Usize.max := by
    intro htype
    rcases htype with ht | ht
    · simp only [GlobalShape, ht] at hcanonical
      exact hcanonical.1.word_bound s .FuncRef global.lo
    · simp only [GlobalShape, ht] at hcanonical
      exact hcanonical.1.word_bound s .ExternRef global.lo
  step with decode_value_boundary global.ty.valtype global.lo global.hi s.id href as ⟨value, hraw, hvalue⟩
  exact ⟨value, rfl, by simpa [hglobal] using hraw, by simpa [hglobal, decodeGlobal] using hvalue⟩

/-- A successful table lookup observes precisely the selected reference in the
decoded table; the concrete reference carries the issuing store identity. -/
theorem table_read_boundary {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (s : runtime.store.Store M) (hs : Shape view s)
    (tableIndex : Usize) (index : U32) (htable : tableIndex.val < s.tables.length)
    (hindex : index.val < (s.tables.val[tableIndex.val]).elements.length) :
    runtime.store.Store.table_get ops s ⟨s.id, tableIndex⟩ index ⦃ answer =>
      ∃ value, answer = .Ok value ∧
        Interp.sourceValue value = refVal
          (decodeRef (s.tables.val[tableIndex.val]).ty
            ((s.tables.val[tableIndex.val]).elements.val[index.val])) ⦄ := by
  unfold runtime.store.Store.table_get
  simp [runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch]
  step as ⟨table, htableEq⟩
  simp [lift]
  split
  · scalar_tac
  · step as ⟨word, hword⟩
    have hcanonical := (hs.tables table (by simp [htableEq])).2.2 word (by simp [hword])
    have href : elementValueType table.ty = .FuncRef ∨ elementValueType table.ty = .ExternRef → word.val ≤ Usize.max := by
      intro _
      exact hcanonical.word_bound s table.ty word
    step with decode_value_boundary (elementValueType table.ty) word 0#u64 s.id href as ⟨value, hraw, hvalue⟩
    refine ⟨value, rfl, ?_⟩
    subst table
    have hword' : word = (s.tables.val[tableIndex.val]).elements.val[index.val] := by simpa using hword
    rw [← hword']
    cases ht : (s.tables.val[tableIndex.val]).ty <;> simpa [elementValueType, ht, decodeWords] using hvalue

end Exec.Store
