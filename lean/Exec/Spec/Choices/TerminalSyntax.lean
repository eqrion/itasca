import Exec.Spec.Choices.TrapNormalization
import Exec.Spec.Choices.ValuePrefixSyntax
/-! A source reduction cannot begin at an operand-only, branch, or return
sequence. This concerns ordinary source syntax, not interpreter progress. -/
namespace Exec.Spec
open SpecExt

def firstOperation : List admininstr → Option Nat
  | [] => none
  | .CONST _ _::tail | .VCONST _ _::tail | .REF_NULL _::tail
  | .REF_FUNC_ADDR _::tail | .REF_HOST_ADDR _::tail => firstOperation tail
  | head::_ => some head.ctorIdx

theorem firstOperation_value (value : val) (tail : List admininstr) :
    firstOperation (admininstr_val value::tail)=firstOperation tail := by
  cases value <;> rfl

theorem firstOperation_vals (values : List val) (tail : List admininstr) :
    firstOperation (vals values++tail)=firstOperation tail := by
  induction values with
  | nil => rfl
  | cons value values ih => simpa only [vals,Map,List.map_cons,List.cons_append,firstOperation_value] using ih

theorem firstOperation_map (values : List val) (tail : List admininstr) :
    firstOperation (Map (fun value => admininstr_val value) values++tail)=firstOperation tail :=
  firstOperation_vals values tail

theorem firstOperation_append (front tail : List admininstr) :
    firstOperation (front++tail)=(firstOperation front).or (firstOperation tail) := by
  induction front with
  | nil => rfl
  | cons instruction rest ih =>
    cases instruction <;> simp_all only [List.cons_append,firstOperation,Option.or]

set_option maxHeartbeats 2000000 in
theorem pure_firstOperation {before after : List admininstr} (source : Step_pure before after) :
    firstOperation before≠none ∧ firstOperation before≠some (admininstr.BR (.mk_uN 0)).ctorIdx ∧
      firstOperation before≠some admininstr.RETURN.ctorIdx := by
  cases source
  all_goals try { simp [firstOperation,admininstr.ctorIdx,firstOperation_value,firstOperation_vals,firstOperation_map] }
  all_goals try { casesm* ref; all_goals simp [admininstr_ref,firstOperation,admininstr.ctorIdx] }

set_option maxHeartbeats 2000000 in
theorem read_firstOperation {before : config} {after : List admininstr} (source : Step_read before after) :
    firstOperation (trapCode before)≠none ∧
      firstOperation (trapCode before)≠some (admininstr.BR (.mk_uN 0)).ctorIdx ∧
      firstOperation (trapCode before)≠some admininstr.RETURN.ctorIdx := by
  cases source
  all_goals simp [trapCode,firstOperation,admininstr.ctorIdx,firstOperation_value,firstOperation_vals,firstOperation_map]

set_option maxHeartbeats 2000000 in
theorem step_firstOperation {before after : config} (source : Step before after) :
    firstOperation (trapCode before)≠none ∧
      firstOperation (trapCode before)≠some (admininstr.BR (.mk_uN 0)).ctorIdx ∧
      firstOperation (trapCode before)≠some admininstr.RETURN.ctorIdx := by
  induction source
  case pure z body result source input output => exact pure_firstOperation source
  case read z body result source input output => exact read_firstOperation source
  case ctxt_instrs z front body tail next result source nonempty input output inside outside ih =>
    dsimp only [trapCode] at *
    simp only [firstOperation_map,firstOperation_vals]
    simp only [firstOperation_append]
    cases same : firstOperation body with
    | none => exact False.elim (ih.1 same)
    | some tag => simpa only [same,Option.or] using ih
  all_goals try { simp [trapCode,firstOperation,admininstr.ctorIdx,firstOperation_value,firstOperation_vals,firstOperation_map] }
  all_goals try { casesm* ref; all_goals simp [trapCode,admininstr_ref,firstOperation,admininstr.ctorIdx] }

theorem step_no_values {state : _root_.state} {values : List val} {after : config} :
    ¬ Step ⟨state,vals values⟩ after := by
  intro source
  have ready := (step_firstOperation source).1
  have empty : firstOperation (vals values)=none := by
    simpa only [List.append_nil,firstOperation] using firstOperation_vals values []
  exact ready empty

theorem step_no_branch {state : _root_.state} {values : List val} {index : idx}
    {tail : List admininstr} {after : config} :
    ¬ Step ⟨state,vals values++(.BR index::tail)⟩ after := by
  intro source
  have ready := (step_firstOperation source).2.1
  apply ready
  simp only [trapCode,firstOperation_vals,firstOperation,admininstr.ctorIdx]

theorem step_no_return {state : _root_.state} {values : List val}
    {tail : List admininstr} {after : config} :
    ¬ Step ⟨state,vals values++(.RETURN::tail)⟩ after := by
  intro source
  have ready := (step_firstOperation source).2.2
  apply ready
  simp only [trapCode,firstOperation_vals,firstOperation,admininstr.ctorIdx]

theorem activeTrap_minimum_size {code : List admininstr} (active : activeTrap code=true) :
    sizeOf ([admininstr.TRAP])≤sizeOf code := by
  cases code with
  | nil => simp [activeTrap] at active
  | cons instruction tail =>
    have headPositive : 0<sizeOf instruction := by cases instruction <;> simp
    have tailPositive := sizeOf_admin_positive tail
    change 3≤1+sizeOf instruction+sizeOf tail
    omega

theorem step_no_trap {state : _root_.state} {after : config} : ¬Step ⟨state,[.TRAP]⟩ after := by
  intro source
  have decreased := step_active_trap source (by simp [trapCode,activeTrap])
  have minimum := activeTrap_minimum_size decreased.2.1
  have smaller := decreased.2.2
  change sizeOf (trapCode after)<sizeOf ([admininstr.TRAP]) at smaller
  omega

set_option maxHeartbeats 2000000 in
theorem stepH_firstOperation {before after : config} {events : List HostEvent}
    (source : StepH before events after) :
    firstOperation (trapCode before)≠none ∧
      firstOperation (trapCode before)≠some (admininstr.BR (.mk_uN 0)).ctorIdx ∧
      firstOperation (trapCode before)≠some admininstr.RETURN.ctorIdx := by
  induction source
  case step source => exact step_firstOperation source
  case ctxt_instrs source nonempty input output inside outside ih =>
    dsimp only [trapCode] at *
    simp only [firstOperation_map,firstOperation_vals]
    simp only [firstOperation_append]
    cases same : firstOperation _ with
    | none => exact False.elim (ih.1 same)
    | some tag => simpa only [same,Option.or] using ih
  all_goals simp [trapCode,firstOperation,admininstr.ctorIdx,firstOperation_value,firstOperation_map,firstOperation_vals]

theorem stepH_no_values {state : _root_.state} {values : List val} {events : List HostEvent} {after : config} :
    ¬ StepH ⟨state,vals values⟩ events after := by
  intro source
  have ready := (stepH_firstOperation source).1
  apply ready
  change firstOperation (vals values)=none
  simpa only [List.append_nil,firstOperation] using firstOperation_vals values []

theorem stepH_no_trap {state : _root_.state} {events : List HostEvent} {after : config} :
    ¬ StepH ⟨state,[.TRAP]⟩ events after := by
  intro source
  obtain ⟨_,ordinary⟩ := stepH_active_ordinary source (by simp [trapCode,activeTrap])
  exact step_no_trap ordinary
end Exec.Spec
