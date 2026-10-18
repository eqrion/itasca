import Exec.Interp.Machines.Core.CoreHeadCoverage
import Exec.Interp.Numeric.Float.FloatPoint
namespace Exec.Interp
open Aeneas.Std
theorem floatCoreCodeRel_head_coverage {C returns locals code labels stack op source next output}
    (ready : ReadyInstruction op) :
    ∀ pc, Code.StructuredCode (Code.FloatCoreEmission C) C.TYPES C.FUNCS returns locals code labels stack
      (op::source) pc next output → (CoreDispatchHead op ∨ ∃ scalar : Abs.Float.Instruction, op = scalar.source) := by
  intro pc relation
  generalize measureEq : code.length-pc = measure
  induction measure using Nat.strong_induction_on generalizing pc with
  | h measure ih =>
    cases relation with
    | linear head fragment rest => cases head with
      | core original => exact Or.inl (coreEmission_ready_head original ready)
      | scalar => exact Or.inr ⟨_,rfl⟩
    | skip forward fetched rest =>
      have bound := rest.entry_bound
      exact ih _ (by omega) _ rest rfl
    | block => exact False.elim ready
    | loop => exact Or.inl (.pure (.loop _ _))
    | ifElse => exact Or.inl (.pure (.ordinary (.ifElse _ _ _)))
    | branch => exact Or.inl (.pure (.ordinary (.branch _)))
    | branchIf => exact Or.inl (.pure (.ordinary (.branchIf _)))
    | call => exact Or.inl (.pure (.call _))
    | unreachable => exact Or.inl (.pure .unreachable)
    | return_ => exact Or.inl (.pure .return_)

theorem float_core_head_coverage {sourceStore raw f compiled C targets next output}
    (point : FloatFramePoint sourceStore raw f compiled C targets next output)
    (ready : ReadySource f) (op : instr) (after : List instr) (code : f.code = op::after) :
    CoreDispatchHead op ∨ ∃ scalar : Abs.Float.Instruction, op = scalar.source := by
  have readyOp : ReadyInstruction op := by
    cases op <;> simp_all only [ReadyInstruction,ReadySource,code]
  exact floatCoreCodeRel_head_coverage readyOp raw.pc.val (by simpa only [code] using point.code.current)
end Exec.Interp
