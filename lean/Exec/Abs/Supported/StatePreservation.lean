import Exec.Abs.Cumulative.StatePreservation
import Exec.Abs.Supported.PureCoverage
namespace Exec.Abs.Supported
open Exec.Abs.Core

/-- Successful instructions retain the supported source grammar, including
unchanged defined function bodies after mutable object-content writes. -/
theorem core_instruction_covered (language : Language allowed) (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (descriptor : CoreInstr op)
    (typed : FrameTyped s {f with code := op :: after} [])
    (covered : SupportedState allowed ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩)
    (equation : instruction s ambient f rest op after = .next next) : SupportedState allowed next := by
  have frame := covered.active {f with code := op :: after} (by simp)
  have tail : Forall allowed after := fun i member => frame.1 i (by simp [member])
  have labels := frame.2
  cases descriptor with
  | slice pure =>
    rw [instruction_slice s ambient f rest _ after pure typed] at equation
    exact slice_instruction_covered s ambient f rest _ after next pure language covered equation
  | constant ty value => exact advance_covered covered equation ⟨tail,labels⟩
  | select =>
    simp only [instruction,select] at equation
    repeat' first | split at equation | contradiction
    all_goals exact advance_covered covered equation ⟨tail,labels⟩
  | global_get index =>
    cases index
    simp only [instruction,globalGet] at equation
    repeat' first | split at equation | contradiction
    all_goals exact advance_covered covered equation ⟨tail,labels⟩
  | global_set index =>
    cases index
    simp only [instruction,globalSet] at equation
    repeat' first | split at equation | contradiction
    all_goals
      refine advance_covered ?_ equation ⟨tail,labels⟩
      exact ⟨covered.active,covered.functions⟩
  | load descriptor argument =>
    rw [instruction_load] at equation
    simp only [load] at equation
    repeat' first | split at equation | contradiction
    all_goals exact advance_covered covered equation ⟨tail,labels⟩
  | store descriptor argument =>
    rw [instruction_store] at equation
    simp only [Core.store] at equation
    repeat' first | split at equation | contradiction
    all_goals
      refine advance_covered ?_ equation ⟨tail,labels⟩
      exact ⟨covered.active,covered.functions⟩
  | block bt body bodyCore =>
    have bodyCore : Forall allowed body := fun i member => language.cumulative (.of_core (bodyCore i member))
    simp only [instruction,astep,enterLabel,Bool.false_eq_true,ite_false] at equation
    repeat' first | split at equation | contradiction
    all_goals
      apply advance_covered covered equation
      refine ⟨bodyCore,?_⟩
      intro label member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨by simp [Forall],tail⟩
      · exact labels label member
  | loop bt body bodyCore =>
    have bodyCore : Forall allowed body := fun i member => language.cumulative (.of_core (bodyCore i member))
    simp only [instruction,astep,enterLabel,ite_true] at equation
    repeat' first | split at equation | contradiction
    all_goals
      apply advance_covered covered equation
      refine ⟨bodyCore,?_⟩
      intro label member
      rcases List.mem_cons.mp member with rfl | member
      · refine ⟨?_,tail⟩
        intro i member
        have same := List.mem_singleton.mp member
        subst i
        exact language.loop bt body bodyCore
      · exact labels label member
  | ifelse bt yes no yesCore noCore =>
    have yesCore : Forall allowed yes := fun i member => language.cumulative (.of_core (yesCore i member))
    have noCore : Forall allowed no := fun i member => language.cumulative (.of_core (noCore i member))
    simp only [instruction,astep] at equation
    repeat' first | split at equation | contradiction
    all_goals
      apply advance_covered covered equation
      refine ⟨?_,labels⟩
      intro i member
      rcases List.mem_cons.mp member with rfl | member
      · apply language.block
        first | assumption | split <;> assumption
      · exact tail i member

theorem float_instruction_covered (language : Language allowed) (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (descriptor : FloatCoreInstr op)
    (typed : FrameTyped s {f with code := op :: after} [])
    (covered : SupportedState allowed ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩)
    (equation : instruction s ambient f rest op after = .next next) : SupportedState allowed next := by
  have frame := covered.active {f with code := op :: after} (by simp)
  have tail : Forall allowed after := fun i member => frame.1 i (by simp [member])
  have labels := frame.2
  cases descriptor with
  | core allowed => exact core_instruction_covered language s ambient f rest op after next allowed typed covered equation
  | scalar op => rw [FloatCore.scalar_not_core] at equation; contradiction
  | block bt body bodyCore =>
    have bodyCore : Forall allowed body := fun i member => language.cumulative (.core (bodyCore i member))
    simp only [instruction,astep,enterLabel,Bool.false_eq_true,ite_false] at equation
    repeat' first | split at equation | contradiction
    all_goals
      apply advance_covered covered equation
      refine ⟨bodyCore,?_⟩
      intro label member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨by simp [Forall],tail⟩
      · exact labels label member
  | loop bt body bodyCore =>
    have bodyCore : Forall allowed body := fun i member => language.cumulative (.core (bodyCore i member))
    simp only [instruction,astep,enterLabel,ite_true] at equation
    repeat' first | split at equation | contradiction
    all_goals
      apply advance_covered covered equation
      refine ⟨bodyCore,?_⟩
      intro label member
      rcases List.mem_cons.mp member with rfl | member
      · refine ⟨?_,tail⟩
        intro i member
        have same := List.mem_singleton.mp member
        subst i
        exact language.loop bt body bodyCore
      · exact labels label member
  | ifelse bt yes no yesCore noCore =>
    have yesCore : Forall allowed yes := fun i member => language.cumulative (.core (yesCore i member))
    have noCore : Forall allowed no := fun i member => language.cumulative (.core (noCore i member))
    simp only [instruction,astep] at equation
    repeat' first | split at equation | contradiction
    all_goals
      apply advance_covered covered equation
      refine ⟨?_,labels⟩
      intro i member
      rcases List.mem_cons.mp member with rfl | member
      · apply language.block
        first | assumption | split <;> assumption
      · exact tail i member


theorem instruction_covered (language : Language allowed) (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (descriptor : CumulativeInstr op)
    (typed : FrameTyped s {f with code := op :: after} [])
    (covered : SupportedState allowed ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩)
    (equation : instruction s ambient f rest op after = .next next) : SupportedState allowed next := by
  have frame := covered.active {f with code := op :: after} (by simp)
  have tail : Forall allowed after := fun i member => frame.1 i (by simp [member])
  have labels := frame.2
  cases descriptor with
  | core allowed => exact float_instruction_covered language s ambient f rest op after next allowed typed covered equation
  | stateful op => rw [Cumulative.stateful_not_core] at equation; contradiction
  | indirect_call table type => rw [Cumulative.indirect_not_core] at equation; contradiction
  | block bt body bodyCore =>
    have bodyCore : Forall allowed body := fun i member => language.cumulative (bodyCore i member)
    simp only [instruction,astep,enterLabel,Bool.false_eq_true,ite_false] at equation
    repeat' first | split at equation | contradiction
    all_goals
      apply advance_covered covered equation
      refine ⟨bodyCore,?_⟩
      intro label member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨by simp [Forall],tail⟩
      · exact labels label member
  | loop bt body bodyCore =>
    have bodyCore : Forall allowed body := fun i member => language.cumulative (bodyCore i member)
    simp only [instruction,astep,enterLabel,ite_true] at equation
    repeat' first | split at equation | contradiction
    all_goals
      apply advance_covered covered equation
      refine ⟨bodyCore,?_⟩
      intro label member
      rcases List.mem_cons.mp member with rfl | member
      · refine ⟨?_,tail⟩
        intro i member
        have same := List.mem_singleton.mp member
        subst i
        exact language.loop bt body bodyCore
      · exact labels label member
  | ifelse bt yes no yesCore noCore =>
    have yesCore : Forall allowed yes := fun i member => language.cumulative (yesCore i member)
    have noCore : Forall allowed no := fun i member => language.cumulative (noCore i member)
    simp only [instruction,astep] at equation
    repeat' first | split at equation | contradiction
    all_goals
      apply advance_covered covered equation
      refine ⟨?_,labels⟩
      intro i member
      rcases List.mem_cons.mp member with rfl | member
      · apply language.block
        first | assumption | split <;> assumption
      · exact tail i member


theorem head_covered (language : Language allowed) (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (descriptor : CoreHead op)
    (typed : FrameTyped s {f with code := op :: after} [])
    (covered : SupportedState allowed ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩)
    (equation : instruction s ambient f rest op after = .next next) : SupportedState allowed next := by
  have frame := covered.active {f with code := op :: after} (by simp)
  have tail : Forall allowed after := fun i member => frame.1 i (by simp [member])
  have labels := frame.2
  cases descriptor with
  | cumulative old => exact instruction_covered language s ambient f rest op after next old typed covered equation
  | external impossible => rw [impossible] at equation; contradiction
  | block bt body =>
    have bodyCore := language.block_body (frame.1 _ (List.mem_cons_self ..))
    simp only [instruction,astep,enterLabel,Bool.false_eq_true,ite_false] at equation
    repeat' first | split at equation | contradiction
    all_goals
      apply advance_covered covered equation
      refine ⟨bodyCore,?_⟩
      intro label member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨by simp [Forall],tail⟩
      · exact labels label member
  | loop bt body =>
    have bodyCore := language.loop_body (frame.1 _ (List.mem_cons_self ..))
    simp only [instruction,astep,enterLabel,ite_true] at equation
    repeat' first | split at equation | contradiction
    all_goals
      apply advance_covered covered equation
      refine ⟨bodyCore,?_⟩
      intro label member
      rcases List.mem_cons.mp member with rfl | member
      · refine ⟨?_,tail⟩
        intro i member
        have same := List.mem_singleton.mp member
        subst i
        exact language.loop bt body bodyCore
      · exact labels label member
  | ifelse bt yes no =>
    obtain ⟨yesCore,noCore⟩ := language.if_bodies (frame.1 _ (List.mem_cons_self ..))
    simp only [instruction,astep] at equation
    repeat' first | split at equation | contradiction
    all_goals
      apply advance_covered covered equation
      refine ⟨?_,labels⟩
      intro i member
      rcases List.mem_cons.mp member with rfl | member
      · apply language.block
        first | assumption | split <;> assumption
      · exact tail i member


/-- The source grammar and retained function-body coverage survive every
successful Core transition; no immutable-store assumption is used. -/
theorem step_covered (language : Language allowed) (s next : AState) (typed : ATyped s) (covered : SupportedState allowed s)
    (equation : step s = .next next) : SupportedState allowed next := by
  rcases s with ⟨source,ambient,frames,results⟩
  cases frames with
  | nil => simp [step] at equation
  | cons frame rest =>
    have noResults := typed.activeResults (by simp)
    change results = [] at noResults
    subst results
    have frameTyped : FrameTyped source frame [] := by
      cases typed.frames with | cons head _ => exact head
    have body := covered.active frame (by simp)
    cases frame with
    | mk address resultTypes locals module labels code values =>
      let frame : AFrame := ⟨address,resultTypes,locals,module,labels,code,values⟩
      cases code with
      | cons op after =>
        exact head_covered language source ambient frame rest op after next (language.head (body.1 op (by simp))) frameTyped covered equation
      | nil =>
        cases labels with
        | nil => exact returnFrame_covered covered equation
        | cons label labels =>
          simp only [step,astep] at equation
          split at equation
          · apply advance_covered covered equation
            exact ⟨(body.2 label (by simp)).2,fun outer member => body.2 outer (by simp [member])⟩
          · contradiction

end Exec.Abs.Supported
