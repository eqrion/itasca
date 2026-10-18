import Exec.Interp.Machines.Core.CoreHeadCoverage
import Exec.Interp.Cumulative.Machine
import Exec.Code.Body.Control.Table.CumulativeTableExclusion
import Exec.Code.Local.Control.Table.StructuredCodeTableLegacy
namespace Exec.Interp
open Aeneas.Std

/-- Exact executable head classification from the retained cumulative bytecode
certificate, including the function-local indirect-call metadata indices. -/
inductive CumulativeDispatchHead : instr → Prop where
  | core {op} : CoreDispatchHead op → CumulativeDispatchHead op
  | scalar (op : Abs.Float.Instruction) : CumulativeDispatchHead op.source
  | stateful (op : Abs.Stateful.Instruction) : CumulativeDispatchHead op.source
  | indirect (table type : U32) : CumulativeDispatchHead (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val))

theorem cumulativeCodeRel_head_coverage {pairs C returns locals code labels stack op source next output}
    (ready : ReadyInstruction op) :
    ∀ pc, Code.StructuredCode (Code.CumulativeEmission pairs C) C.TYPES C.FUNCS returns locals code labels stack
      (op::source) pc next output → CumulativeDispatchHead op := by
  intro pc relation
  generalize measureEq : code.length-pc = measure
  induction measure using Nat.strong_induction_on generalizing pc with
  | h measure ih =>
    cases relation with
    | linear head fragment rest => cases head with
      | left head => cases head with
        | core original => exact .core (coreEmission_ready_head original ready)
        | scalar => exact .scalar _
      | right head => cases head;exact .stateful _
      | indirect head => cases head;exact .indirect _ _
    | skip forward fetched rest =>
      have bound := rest.entry_bound
      exact ih _ (by omega) _ rest rfl
    | block => exact False.elim ready
    | loop => exact .core (.pure (.loop _ _))
    | ifElse => exact .core (.pure (.ordinary (.ifElse _ _ _)))
    | branch => exact .core (.pure (.ordinary (.branch _)))
    | branchIf => exact .core (.pure (.ordinary (.branchIf _)))
    | call => exact .core (.pure (.call _))
    | unreachable => exact .core (.pure .unreachable)
    | return_ => exact .core (.pure .return_)

theorem cumulative_head_coverage {sourceStore raw f compiled C targets next output}
    (point : Cumulative.FramePoint sourceStore raw f compiled C targets next output)
    (ready : ReadySource f) (op : instr) (after : List instr) (code : f.code=op::after) :
    CumulativeDispatchHead op := by
  have readyOp : ReadyInstruction op := by
    cases op <;> simp_all only [ReadyInstruction,ReadySource,code]
  exact cumulativeCodeRel_head_coverage readyOp raw.pc.val (by simpa only [code,Cumulative.emission] using point.code.current.to_old (fun _ depths fallback _ _ _ h => h.not_branchTable depths fallback rfl))
end Exec.Interp
