import Exec.Interp.StructuredMachine.ErasedHeads
import Exec.Abs.FloatCore
import Exec.Code.Local.Relations.Calls.IndirectCallEmission
namespace Exec.Interp.StructuredMachine

instance {pairs} : OrdinaryHeads (Code.IndirectCallEmission pairs) where
  ordinary := by intro C before instruction emitted after head; cases head; rfl

instance {pairs} : ErasedHeads (Code.IndirectCallEmission pairs) where
  nop := by intro C before after emitted head; cases head
  drop := by intro C before after emitted head; cases head

private theorem slice_not_indirect {table type} (covered : Abs.SliceInstr (.CALL_INDIRECT table type)) : False := by
  generalize equal : instr.CALL_INDIRECT table type = instruction at covered
  cases covered with
  | numeric op => cases op <;> cases equal
  | _ => cases equal

private theorem core_not_indirect {table type} (covered : Abs.CoreInstr (.CALL_INDIRECT table type)) : False := by
  generalize equal : instr.CALL_INDIRECT table type = instruction at covered
  cases covered with
  | slice h => rw [← equal] at h; exact slice_not_indirect h
  | load op arg => cases op <;> cases equal
  | store op arg => cases op <;> cases equal
  | _ => cases equal

theorem float_core_not_indirect {table type} (covered : Abs.FloatCoreInstr (.CALL_INDIRECT table type)) : False := by
  generalize equal : instr.CALL_INDIRECT table type = instruction at covered
  cases covered with
  | core h => rw [← equal] at h; exact core_not_indirect h
  | scalar op => cases op <;> cases equal
  | _ => cases equal

end Exec.Interp.StructuredMachine
