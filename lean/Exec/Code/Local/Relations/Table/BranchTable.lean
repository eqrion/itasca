import Exec.Code.Local.Control.Common.StructuredCode
import Exec.Code.Local.Relations.Table.BranchTableLayout
import Exec.Code.Local.Callbacks.Table.CompilerTables
import Exec.Abs.BrTable
namespace Exec.Code
open Aeneas.Std

/-- Compatibility view of the indexed branch-table layout. -/
abbrev BranchTableCode (tables : CompilerTables) := BranchTableLayout tables.jumpTables

theorem BranchTableEntry.structured {locals labels stack code depth entry next}
    (entryCode : BranchTableEntry locals labels stack code depth entry next)
    (emission : List valtype → instr → List Bytecode → List valtype → Prop)
    (types functions : List functype) (returns : List valtype)
    (after : List instr) (output : List valtype) :
    StructuredCode emission types functions returns locals code labels stack
      (.BR depth :: after) entry.val next output := by
  obtain ⟨label,dst,src,count,fragmentEnd,lookup,live,layout,fragment,remaining,scope⟩ := entryCode
  cases depth with
  | mk_uN depth => exact .branch lookup live layout fragment remaining scope

theorem BranchTableCode.selected {tables locals labels stack code depths fallback pc next selector start len}
    (table : BranchTableCode tables locals labels stack code depths fallback pc next selector start len)
    (value : Nat) :
    ∃ entry, tables.jumpTables[start.val + Nat.min value (len.val-1)]? = some entry ∧
      BranchTableEntry locals labels stack code (Abs.BrTable.select depths fallback value) entry next := by
  obtain ⟨entry,lookup,fragment⟩ := table.entries (Nat.min value depths.length)
    (Abs.BrTable.select depths fallback value) (Abs.BrTable.select_table depths fallback value)
  exact ⟨entry,by simpa only [table.length,Nat.add_sub_cancel] using lookup,fragment⟩

end Exec.Code
