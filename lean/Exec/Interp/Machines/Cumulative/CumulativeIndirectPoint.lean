import Exec.Interp.StructuredMachine.IndirectPoint
import Exec.Code.Local.Control.Calls.CumulativeIndirectInversion
namespace Exec.Interp.Cumulative
open Aeneas.Std
theorem indirect_point_head {pairs C returns code jumpTables labels stack pc next output}
    (table type : Nat) (after : List instr)
    (point : Code.StructuredCodeWithTables.Point (Code.CumulativeEmission pairs C) C.TYPES C.FUNCS returns C.LOCALS
      code jumpTables labels stack (.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCodeWithTables.Point (Code.CumulativeEmission pairs C) C.TYPES C.FUNCS returns C.LOCALS
        code jumpTables labels stack (.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after) target.val next output) ∨
    (∃ (front params results : List valtype) (typeIndex tableIndex entry index base : U32) (bounds : limits),
      typeIndex.val = type ∧ tableIndex.val = table ∧ stack = (front ++ params) ++ [.I32] ∧
      C.TYPES[type]? = some ⟨.mk_list params,.mk_list results⟩ ∧
      C.TABLES[table]? = some (.mk_tabletype bounds .FUNCREF) ∧
      pairs[entry.val]? = some (tableIndex,typeIndex) ∧
      base.val = Code.slots C.LOCALS + Code.slots front ∧ index.val = base.val + Code.slots params ∧
      code[pc]? = some (.CallIndirect entry index base) ∧
      Code.StructuredCodeWithTables.Point (Code.CumulativeEmission pairs C) C.TYPES C.FUNCS returns C.LOCALS
        code jumpTables labels (front ++ results) after (pc+1) next output) := by
  exact StructuredMachine.indirect_point_head table type after (fun _ _ _ head => head.indirect_inv) point
end Exec.Interp.Cumulative
