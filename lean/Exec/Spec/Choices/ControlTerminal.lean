import Exec.Spec.Choices.TerminalOutcomes
namespace Exec.Spec
open SpecExt

theorem stepH_no_branch {state : _root_.state} {values : List val} {index : idx}
    {tail : List admininstr} {events : List HostEvent} {after : config} :
    ¬StepH ⟨state,vals values++(.BR index::tail)⟩ events after := by
  intro source
  have ready := (stepH_firstOperation source).2.1
  apply ready
  simp only [trapCode,firstOperation_vals,firstOperation,admininstr.ctorIdx]

theorem stepH_no_return {state : _root_.state} {values : List val}
    {tail : List admininstr} {events : List HostEvent} {after : config} :
    ¬StepH ⟨state,vals values++(.RETURN::tail)⟩ events after := by
  intro source
  have ready := (stepH_firstOperation source).2.2
  apply ready
  simp only [trapCode,firstOperation_vals,firstOperation,admininstr.ctorIdx]

set_option maxHeartbeats 2000000 in
theorem pure_label_body_terminal {before after : List admininstr} {arity : Nat} {cont : List instr}
    {body : List admininstr} (source : Step_pure before after) (same : before=[.LABEL_ arity cont body])
    (state : _root_.state) (events : List HostEvent) (next : config) : ¬StepH ⟨state,body⟩ events next := by
  have head := congrArg firstOperation same
  cases source
  all_goals try { simp [firstOperation,firstOperation_value,firstOperation_map,admininstr.ctorIdx] at head }
  all_goals try injections
  all_goals subst_vars
  all_goals try { exact stepH_no_values }
  all_goals try { exact stepH_no_trap }
  all_goals try simp only [Map,← List.map_append,List.append_assoc] at *
  all_goals try { exact stepH_no_branch }
  all_goals try { exact stepH_no_return }
set_option maxHeartbeats 2000000 in
theorem pure_frame_body_terminal {before after : List admininstr} {arity : Nat} {frame : _root_.frame}
    {body : List admininstr} (source : Step_pure before after) (same : before=[.FRAME_ arity frame body])
    (state : _root_.state) (events : List HostEvent) (next : config) : ¬StepH ⟨state,body⟩ events next := by
  have head := congrArg firstOperation same
  cases source
  all_goals try { simp [firstOperation,firstOperation_value,firstOperation_map,admininstr.ctorIdx] at head }
  all_goals try injections
  all_goals subst_vars
  all_goals try { exact stepH_no_values }
  all_goals try { exact stepH_no_trap }
  all_goals try simp only [Map,← List.map_append,List.append_assoc] at *
  all_goals try { exact stepH_no_branch }
  all_goals try { exact stepH_no_return }
end Exec.Spec
