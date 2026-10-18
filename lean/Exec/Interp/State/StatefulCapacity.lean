import Exec.Interp.State.StatefulPoint
import Exec.Abs.Stateful.Transition
import Exec.Code.Local.Capacity.OperandBounds
namespace Exec.Interp.Stateful
open Aeneas Aeneas.Std Itasca.ResultFacts

private theorem first_checked (first second : Result Bool)
    (checked : (do let b ← first; if b then second else .ok false) = .ok true) : first=.ok true := by
  obtain ⟨value,run,checked⟩ := bind_ok_inv _ _ _ checked
  cases value with
  | false => simp at checked
  | true => exact run

theorem read_valid_capacity (compiled : runtime.bytecode.CompiledFunction)
    (op : Abs.Stateful.Instruction) (first second a entry : U32)
    (readOnly : op.readOnly=true)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid compiled (Code.statefulInstruction op first second a entry)=.ok true) :
    first.val<compiled.slot_count.val := by
  cases op <;> simp only [Abs.Stateful.Instruction.readOnly,Bool.false_eq_true] at readOnly
  all_goals
    simp only [Code.statefulInstruction,runtime.bytecode.CompiledFunction.instruction_valid,
      runtime.bytecode.Instr.scalar,runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,
      runtime.bytecode.Instr.simd,bind_ok] at checked
  all_goals first
    | (have bound := Code.slots_fit_true compiled first 1#u32 checked; scalar_tac)
    | (have bound := Code.slots_fit_true compiled first 1#u32 (first_checked _ _ checked); scalar_tac)
end Exec.Interp.Stateful
