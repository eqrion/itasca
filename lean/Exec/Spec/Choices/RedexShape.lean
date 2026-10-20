import Exec.Spec.Choices.PureDeterminism
import Exec.Spec.Choices.TerminalSyntax
namespace Exec.Spec
open SpecExt

def residualCode : List admininstr → List admininstr
  | [] => []
  | .CONST _ _::tail | .VCONST _ _::tail | .REF_NULL _::tail
  | .REF_FUNC_ADDR _::tail | .REF_HOST_ADDR _::tail => residualCode tail
  | head::tail => head::tail

theorem residualCode_value (value : val) (tail : List admininstr) :
    residualCode (admininstr_val value::tail)=residualCode tail := by cases value <;> rfl

theorem residualCode_vals (values : List val) (tail : List admininstr) :
    residualCode (vals values++tail)=residualCode tail := by
  induction values with
  | nil => rfl
  | cons value values ih => simpa only [vals,Map,List.map_cons,List.cons_append,residualCode_value] using ih

theorem residualCode_map (values : List val) (tail : List admininstr) :
    residualCode (Map (fun value => admininstr_val value) values++tail)=residualCode tail := residualCode_vals values tail

set_option maxHeartbeats 2000000 in
theorem pure_residual_single {before after : List admininstr} (source : Step_pure before after)
    (nonactive : activeTrap before=false) : (residualCode before).length=1 := by
  cases source
  all_goals try { simp [activeTrap,activeTrap_value,activeTrap_map] at nonactive }
  all_goals try { simp [residualCode,residualCode_value,residualCode_map] }
  all_goals try { casesm* ref; all_goals simp [admininstr_ref,residualCode] }

set_option maxHeartbeats 2000000 in
theorem read_residual_single {before : config} {after : List admininstr} (source : Step_read before after) :
    (residualCode (trapCode before)).length=1 := by
  cases source
  all_goals simp [trapCode,residualCode,residualCode_value,residualCode_map]
end Exec.Spec
