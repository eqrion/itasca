import Exec.Interp.StructuredMachine.Point
import Exec.Code.Local.Relations.Table.BranchTable
namespace Exec.Interp.StructuredMachine
open Aeneas.Std

theorem branchTable_point_head {emit types functions returns locals code jumpTables labels stack pc next output depths fallback after}
    (point : Code.StructuredCodeWithTables.Point emit types functions returns locals code jumpTables labels stack
      (.BR_TABLE depths fallback::after) pc next output) :
    (∃ target : U32, pc<target.val ∧ code[pc]?=some (.Jump target) ∧
      Code.StructuredCodeWithTables.Point emit types functions returns locals code jumpTables labels stack
        (.BR_TABLE depths fallback::after) target.val next output) ∨
    (∃ front selector start len, stack=front++[.I32] ∧
      Code.BranchTableLayout jumpTables locals labels front code depths fallback pc next selector start len) := by
  cases point.current with
  | linear head ordinary fragment rest => exact False.elim (ordinary depths fallback rfl)
  | skip forward fetched rest =>
    exact Or.inl ⟨_,forward,fetched,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | branchTable gate table bounds => exact Or.inr ⟨_,_,_,_,rfl,table⟩

end Exec.Interp.StructuredMachine
namespace Exec.Code
open Aeneas.Std

theorem BranchTableEntry.structured_indexed {locals labels stack code depth entry next}
    (entryCode : BranchTableEntry locals labels stack code depth entry next)
    (emission : List valtype → instr → List Bytecode → List valtype → Prop)
    (types functions : List functype) (returns : List valtype) (jumpTables : List U32)
    (after : List instr) (output : List valtype) :
    StructuredCodeWithTables emission types functions returns locals code jumpTables labels stack
      (.BR depth :: after) entry.val next output := by
  obtain ⟨label,dst,src,count,fragmentEnd,lookup,live,layout,fragment,remaining,scope⟩ := entryCode
  cases depth with
  | mk_uN depth => exact .branch lookup live layout fragment remaining scope
end Exec.Code
