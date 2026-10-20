import Exec.Spec.Choices.ChosenPureNeutral
import Exec.Spec.Choices.TerminalSyntax
namespace Exec.Spec

/-- Inspect the active instruction through value prefixes, labels and frames.
Suspended continuations do not consume numeric or growth replies. Host replies are excluded separately by their events. -/
def neutralActive : List admininstr → Bool
  | [] => true
  | .CONST _ _::tail | .VCONST _ _::tail | .REF_NULL _::tail
  | .REF_FUNC_ADDR _::tail | .REF_HOST_ADDR _::tail => neutralActive tail
  | .LABEL_ _ _ body::_ | .FRAME_ _ _ body::_ => neutralActive body
  | .UNOP _ _::_ | .BINOP _ _::_ | .CVTOP _ _ _::_ | .VCVTOP _ _ _::_
  | .MEMORY_GROW::_ | .TABLE_GROW _::_ => false
  | .VUNOP _ op::_ => !vectorUnaryFloat op
  | .VBINOP _ op::_ => !vectorBinaryFloat op
  | _ => true
termination_by body => sizeOf body

theorem neutralActive_value (value : val) (tail : List admininstr) :
    neutralActive (admininstr_val value::tail)=neutralActive tail := by cases value <;> simp only [admininstr_val,neutralActive]

theorem neutralActive_vals (values : List val) (tail : List admininstr) :
    neutralActive (SpecExt.vals values++tail)=neutralActive tail := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simpa only [SpecExt.vals,Map,List.map_cons,List.cons_append,neutralActive_value] using ih

theorem neutralActive_append (front tail : List admininstr) :
    neutralActive (front++tail)=if firstOperation front=none then neutralActive tail else neutralActive front := by
  induction front with
  | nil => rfl
  | cons head front ih =>
    cases head
    all_goals first
      | simpa only [List.cons_append,neutralActive,firstOperation] using ih
      | simp [List.cons_append,neutralActive,firstOperation]

theorem neutralActive_pure {body : List admininstr} (neutral : neutralActive body=true) :
    neutralPureRedex body=true := by
  unfold neutralPureRedex
  split <;> simp_all [neutralActive]
end Exec.Spec
