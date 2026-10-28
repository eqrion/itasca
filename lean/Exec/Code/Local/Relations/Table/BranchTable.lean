import Exec.Code.Local.Control.Common.Structured
import Exec.Code.Local.Relations.Table.BranchTableLayout
import Exec.Code.Local.Callbacks.Table.CompilerTables
import Exec.Abs.BrTable
namespace Itasca.Runtime.Code
open Aeneas.Std

/-- Compatibility view of the indexed branch-table layout. -/
abbrev BranchTableCode (tables : CompilerTables) := BranchTableLayout tables.jumpTables

theorem BranchTableCode.selected {tables locals labels stack code depths fallback pc next selector start len}
    (table : BranchTableCode tables locals labels stack code depths fallback pc next selector start len)
    (value : Nat) :
    ∃ entry, tables.jumpTables[start.val + Nat.min value (len.val-1)]? = some entry ∧
      BranchTableEntry locals labels stack code (Abs.BrTable.select depths fallback value) entry next := by
  obtain ⟨entry,lookup,fragment⟩ := table.entries (Nat.min value depths.length)
    (Abs.BrTable.select depths fallback value) (Abs.BrTable.select_table depths fallback value)
  exact ⟨entry,by simpa only [table.length,Nat.add_sub_cancel] using lookup,fragment⟩

end Itasca.Runtime.Code
