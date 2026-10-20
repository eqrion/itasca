import Exec.Spec.Choices.TrapAdministrative
import Exec.Spec.EventfulInfinite

/-! Active traps admit only administrative cleanup: syntax strictly decreases,
finite prefixes retain the exact state and empty host history, and infinite
cleanup is impossible. These facts do not assume source-step determinism. -/
namespace Exec.Spec
open SpecExt

def trapCode : config → List admininstr
  | ⟨_,code⟩ => code

def trapState : config → state
  | ⟨state,_⟩ => state


def activeTrap : List admininstr → Bool
  | [] => false
  | .CONST _ _::tail | .VCONST _ _::tail | .REF_NULL _::tail
  | .REF_FUNC_ADDR _::tail | .REF_HOST_ADDR _::tail => activeTrap tail
  | .TRAP::_ => true
  | .LABEL_ _ _ body::_ | .FRAME_ _ _ body::_ => activeTrap body
  | _ => false
termination_by code => sizeOf code

theorem activeTrap_value (value : val) (tail : List admininstr) :
    activeTrap (admininstr_val value::tail)=activeTrap tail := by cases value <;> simp [activeTrap,admininstr_val]

theorem activeTrap_vals (values : List val) (tail : List admininstr) :
    activeTrap (vals values++tail)=activeTrap tail := by
  induction values with
  | nil => rfl
  | cons value values ih => simpa only [vals,Map,List.map_cons,List.cons_append,activeTrap_value] using ih

theorem activeTrap_values (values : List val) : activeTrap (vals values)=false := by
  simpa only [List.append_nil,activeTrap] using activeTrap_vals values []

theorem activeTrap_map (values : List val) (tail : List admininstr) :
    activeTrap (Map (fun v => admininstr_val v) values++tail)=activeTrap tail := activeTrap_vals values tail

theorem activeTrap_map_nil (values : List val) :
    activeTrap (Map (fun v => admininstr_val v) values)=false := activeTrap_values values

theorem sizeOf_admin_append (front tail : List admininstr) :
    sizeOf (front++tail)+1=sizeOf front+sizeOf tail := by
  induction front with
  | nil => simp [Nat.add_comm]
  | cons head front ih => simp only [List.cons_append,List.cons.sizeOf_spec]; omega

theorem sizeOf_admin_positive (code : List admininstr) : 0<sizeOf code := by
  cases code <;> simp only [List.cons.sizeOf_spec,List.nil.sizeOf_spec] <;> omega

set_option maxHeartbeats 4000000 in
theorem pure_active_trap {before after : List admininstr} (source : Step_pure before after)
    (active : activeTrap before=true) : after=[.TRAP] ∧ sizeOf after<sizeOf before := by
  cases source
  all_goals try { simp [activeTrap,activeTrap_value,List.append_assoc,activeTrap_map,activeTrap_map_nil] at active }

  case trap_label | trap_frame =>
    constructor
    · rfl
    · simp only [List.cons.sizeOf_spec,List.nil.sizeOf_spec,admininstr.LABEL_.sizeOf_spec,admininstr.FRAME_.sizeOf_spec,admininstr.TRAP.sizeOf_spec]
      omega
  case trap_vals values tail nonempty _ _ _ =>
    constructor
    · rfl
    · have appendSize := sizeOf_admin_append (vals values) ([.TRAP]++tail)
      have frontPositive := sizeOf_admin_positive (vals values)
      have tailPositive := sizeOf_admin_positive tail
      have nonemptySize : 1<sizeOf (vals values)+sizeOf tail-1 := by
        rcases nonempty with h | h
        · cases values with
          | nil => contradiction
          | cons value values =>
            have positive := sizeOf_admin_positive (vals values)
            simp only [vals,Map,List.map_cons,List.cons.sizeOf_spec] at *
            omega
        · cases tail with
          | nil => contradiction
          | cons instruction tail =>
            have positive := sizeOf_admin_positive tail
            simp only [List.cons.sizeOf_spec] at *
            omega
      change sizeOf ([admininstr.TRAP])<sizeOf (vals values++([.TRAP]++tail))
      simp only [List.cons_append,List.nil_append,List.cons.sizeOf_spec,List.nil.sizeOf_spec,admininstr.TRAP.sizeOf_spec] at *
      omega
  case ref_is_null_true | ref_is_null_false =>
    casesm* ref
    all_goals simp [admininstr_ref,activeTrap] at active

set_option maxHeartbeats 4000000 in
theorem pure_activeTrap_suffix {before after : List admininstr} (source : Step_pure before after)
    (tail : List admininstr) : activeTrap (before++tail)=activeTrap before := by
  cases source
  all_goals try { simp [activeTrap,activeTrap_value,List.append_assoc,activeTrap_map,activeTrap_map_nil] }
  all_goals try { casesm* ref; all_goals simp [trapCode,admininstr_ref,activeTrap] }

set_option maxHeartbeats 4000000 in
theorem read_activeTrap_suffix {state : _root_.state} {before after : List admininstr}
    (source : Step_read ⟨state,before⟩ after) (tail : List admininstr) :
    activeTrap (before++tail)=activeTrap before := by
  cases source
  all_goals try { simp [activeTrap,activeTrap_value,List.append_assoc,activeTrap_map] }

set_option maxHeartbeats 4000000 in
theorem read_no_active_trap {state : _root_.state} {before after : List admininstr}
    (source : Step_read ⟨state,before⟩ after) : activeTrap before=false := by
  cases source
  all_goals try { simp [activeTrap,activeTrap_value,List.append_assoc,activeTrap_map] }

set_option maxHeartbeats 4000000 in
theorem step_activeTrap_suffix {before after : config}
    (source : Step before after) (extra : List admininstr) :
    activeTrap (trapCode before++extra)=activeTrap (trapCode before) := by
  induction source generalizing extra
  case pure z before after pure _ _ => exact pure_activeTrap_suffix pure extra
  case read z before after read _ _ => exact read_activeTrap_suffix read extra
  case ctxt_instrs z front body tail next after source _ _ _ _ _ ih =>
    dsimp only [trapCode] at *
    simp only [List.append_assoc,activeTrap_map]
    rw [ih (tail++extra),ih tail]
  all_goals try { simp [trapCode,activeTrap,activeTrap_value,List.append_assoc,activeTrap_map] }
  all_goals try { casesm* ref; all_goals simp [trapCode,admininstr_ref,activeTrap] }

theorem activeTrap_append_true {code : List admininstr} (active : activeTrap code=true) (tail : List admininstr) :
    activeTrap (code++tail)=true := by
  induction code with
  | nil => simp [activeTrap] at active
  | cons instruction rest ih =>
    cases instruction <;> simp_all only [List.cons_append,activeTrap]

set_option maxHeartbeats 4000000 in
theorem step_active_trap {before after : config} (source : Step before after)
    (active : activeTrap (trapCode before)=true) :
    trapState after=trapState before ∧ activeTrap (trapCode after)=true ∧
      sizeOf (trapCode after)<sizeOf (trapCode before) := by
  induction source
  case pure z before after pure _ _ =>
    obtain ⟨same,decrease⟩ := pure_active_trap pure active
    cases same
    exact ⟨rfl,by simp [trapCode,activeTrap],decrease⟩
  case read z before after read _ _ =>
    have noTrap := read_no_active_trap read
    simp only [trapCode,noTrap] at active
    contradiction
  case ctxt_label z arity cont body next after source _ _ _ _ ih =>
    have bodyActive : activeTrap body=true := by simpa only [trapCode,activeTrap] using active
    obtain ⟨same,postActive,decrease⟩ := ih bodyActive
    refine ⟨same,?_,?_⟩
    · simpa only [trapCode,activeTrap] using postActive
    · dsimp only [trapCode] at *
      simp only [List.cons.sizeOf_spec,List.nil.sizeOf_spec,admininstr.LABEL_.sizeOf_spec]
      omega
  case ctxt_frame s frame arity inner body t next after source _ _ _ _ ih =>
    have bodyActive : activeTrap body=true := by simpa only [trapCode,activeTrap] using active
    obtain ⟨same,postActive,decrease⟩ := ih bodyActive
    change state.mk_state t next=state.mk_state s inner at same
    cases same
    refine ⟨rfl,?_,?_⟩
    · simpa only [trapCode,activeTrap] using postActive
    · dsimp only [trapCode] at *
      simp only [List.cons.sizeOf_spec,List.nil.sizeOf_spec,admininstr.FRAME_.sizeOf_spec]
      omega
  case ctxt_instrs z front body tail next after source _ _ _ _ _ ih =>
    have suffix := step_activeTrap_suffix source tail
    dsimp only [trapCode] at suffix
    have bodyActive : activeTrap body=true := by
      simpa only [trapCode,activeTrap_map,suffix] using active
    obtain ⟨same,postActive,decrease⟩ := ih bodyActive
    refine ⟨same,?_,?_⟩
    · simpa only [trapCode,activeTrap_map] using activeTrap_append_true postActive tail
    · dsimp only [trapCode] at *
      have b := sizeOf_admin_append body tail
      have a := sizeOf_admin_append after tail
      have b' := sizeOf_admin_append (vals front) (body++tail)
      have a' := sizeOf_admin_append (vals front) (after++tail)
      exact Nat.lt_of_add_lt_add_right (by omega : sizeOf (vals front++(after++tail))+1<sizeOf (vals front++(body++tail))+1)
  all_goals try { simp [trapCode,activeTrap,activeTrap_value,List.append_assoc,activeTrap_map] at active }
  all_goals try { casesm* ref; all_goals simp [trapCode,admininstr_ref,activeTrap] at active }

set_option maxHeartbeats 4000000 in
theorem stepH_activeTrap_suffix {before after : config} {events : List HostEvent}
    (source : StepH before events after) (extra : List admininstr) :
    activeTrap (trapCode before++extra)=activeTrap (trapCode before) := by
  induction source generalizing extra with
  | step source => exact step_activeTrap_suffix source extra
  | host_return => simp [trapCode,List.append_assoc,activeTrap_vals,activeTrap]
  | host_trap => simp [trapCode,List.append_assoc,activeTrap_vals,activeTrap]
  | ctxt_label => simp [trapCode,activeTrap]
  | ctxt_frame => simp [trapCode,activeTrap]
  | @ctxt_instrs z z' front body body' tail events source _ _ _ _ _ ih =>
    dsimp only [trapCode] at *
    simp only [List.append_assoc,activeTrap_vals]
    rw [ih (tail++extra),ih tail]

/-- Once a trap is active, no host action or store/frame mutation can occur.
Only ordinary administrative cleanup remains. -/
theorem stepH_active_ordinary {before after : config} {events : List HostEvent}
    (source : StepH before events after) (active : activeTrap (trapCode before)=true) :
    events=[] ∧ Step before after := by
  induction source with
  | step source => exact ⟨rfl,source⟩
  | host_return => simp [trapCode,activeTrap_vals,activeTrap] at active
  | host_trap => simp [trapCode,activeTrap_vals,activeTrap] at active
  | @ctxt_label z z' arity cont body body' events source _ _ _ _ ih =>
    have bodyActive : activeTrap body=true := by simpa only [trapCode,activeTrap] using active
    obtain ⟨empty,ordinary⟩ := ih bodyActive
    refine ⟨empty,?_⟩
    apply Step.ctxt_label <;> assumption
  | @ctxt_frame s t f inner inner' arity body body' events source _ _ _ _ ih =>
    have bodyActive : activeTrap body=true := by simpa only [trapCode,activeTrap] using active
    obtain ⟨empty,ordinary⟩ := ih bodyActive
    refine ⟨empty,?_⟩
    apply Step.ctxt_frame <;> assumption
  | @ctxt_instrs z z' front body body' tail events source _ _ _ _ _ ih =>
    have suffix := stepH_activeTrap_suffix source tail
    dsimp only [trapCode] at suffix
    have bodyActive : activeTrap body=true := by simpa only [trapCode,activeTrap_vals,suffix] using active
    obtain ⟨empty,ordinary⟩ := ih bodyActive
    refine ⟨empty,?_⟩
    apply Step.ctxt_instrs <;> assumption

theorem stepH_active_trap {before after : config} {events : List HostEvent}
    (source : StepH before events after) (active : activeTrap (trapCode before)=true) :
    events=[] ∧ trapState after=trapState before ∧ activeTrap (trapCode after)=true ∧
      sizeOf (trapCode after)<sizeOf (trapCode before) := by
  obtain ⟨empty,ordinary⟩ := stepH_active_ordinary source active
  exact ⟨empty,step_active_trap ordinary active⟩

/-- Counted cleanup steps strictly consume syntax and retain the exact store,
frame and empty host history at every finite prefix. -/
theorem StepsHN.active_trap {count before after events}
    (source : StepsHN count before events after) (active : activeTrap (trapCode before)=true) :
    events=[] ∧ trapState after=trapState before ∧ activeTrap (trapCode after)=true ∧
      sizeOf (trapCode after)+count≤sizeOf (trapCode before) := by
  induction source with
  | refl => exact ⟨rfl,rfl,active,by omega⟩
  | cons edge tail ih =>
    obtain ⟨empty,same,nextActive,decrease⟩ := stepH_active_trap edge active
    obtain ⟨restEmpty,restSame,finalActive,bound⟩ := ih nextActive
    exact ⟨by simp only [empty,restEmpty,List.nil_append],restSame.trans same,finalActive,by omega⟩

/-- Administrative trap cleanup is strongly terminating for every source
scheduler and host policy, independently of semantic configuration typing. -/
theorem active_trap_no_infinite {initial : config} (active : activeTrap (trapCode initial)=true) :
    ¬ InfiniteSourceWithEvents initial := by
  intro infinite
  obtain ⟨states,events,first,edges⟩ := infinite
  have every : ∀ n, activeTrap (trapCode (states n))=true ∧
      sizeOf (trapCode (states n))+n≤sizeOf (trapCode initial) := by
    intro n
    induction n with
    | zero => simpa only [first,Nat.add_zero] using And.intro active (Nat.le_refl (sizeOf (trapCode initial)))
    | succ n ih =>
      obtain ⟨count,positive,chunk⟩ := edges n
      have result := chunk.active_trap ih.1
      exact ⟨result.2.2.1,by omega⟩
  have impossible := (every (sizeOf (trapCode initial)+1)).2
  omega

/-- Every completed cleanup run has the same trap state and no host events. -/
theorem active_trap_outcome {initial : config} {state : _root_.state} {events : List HostEvent}
    (active : activeTrap (trapCode initial)=true) (run : StepsH initial events ⟨state,[.TRAP]⟩) :
    state=trapState initial ∧ events=[] := by
  obtain ⟨count,counted⟩ := stepsH_count run
  have result := counted.active_trap active
  exact ⟨result.2.1,result.1⟩

theorem active_trap_no_values {initial : config} {state : _root_.state} {events : List HostEvent} {values : List val}
    (active : activeTrap (trapCode initial)=true) : ¬ StepsH initial events ⟨state,vals values⟩ := by
  intro run
  obtain ⟨count,counted⟩ := stepsH_count run
  have result := counted.active_trap active
  have impossible := result.2.2.1
  simp only [trapCode,activeTrap_values] at impossible
  contradiction

end Exec.Spec
