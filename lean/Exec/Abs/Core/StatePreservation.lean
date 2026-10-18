import Exec.Abs.Core.PureCoverage
import Exec.Abs.Core.Pure

namespace Exec.Abs.Core

/-- Successful instructions retain the supported source grammar, including
unchanged defined function bodies after mutable object-content writes. -/
theorem instruction_core (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (allowed : CoreInstr op)
    (typed : FrameTyped s {f with code := op :: after} [])
    (covered : CoreState ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩)
    (equation : instruction s ambient f rest op after = .next next) : CoreState next := by
  have frame := covered.active {f with code := op :: after} (by simp)
  have tail : Forall CoreInstr after := fun i member => frame.1 i (by simp [member])
  have labels := frame.2
  cases allowed with
  | slice pure =>
    rw [instruction_slice s ambient f rest _ after pure typed] at equation
    exact Exec.Abs.instruction_core s ambient f rest _ after next pure covered equation
  | constant ty value => exact advance_core covered equation ⟨tail,labels⟩
  | select =>
    simp only [instruction,select] at equation
    repeat' first | split at equation | contradiction
    all_goals exact advance_core covered equation ⟨tail,labels⟩
  | global_get index =>
    cases index
    simp only [instruction,globalGet] at equation
    repeat' first | split at equation | contradiction
    all_goals exact advance_core covered equation ⟨tail,labels⟩
  | global_set index =>
    cases index
    simp only [instruction,globalSet] at equation
    repeat' first | split at equation | contradiction
    all_goals
      refine advance_core ?_ equation ⟨tail,labels⟩
      exact ⟨covered.active,covered.functions⟩
  | load descriptor argument =>
    rw [instruction_load] at equation
    simp only [load] at equation
    repeat' first | split at equation | contradiction
    all_goals exact advance_core covered equation ⟨tail,labels⟩
  | store descriptor argument =>
    rw [instruction_store] at equation
    simp only [store] at equation
    repeat' first | split at equation | contradiction
    all_goals
      refine advance_core ?_ equation ⟨tail,labels⟩
      exact ⟨covered.active,covered.functions⟩
  | block bt body bodyCore =>
    simp only [instruction,astep,enterLabel,Bool.false_eq_true,ite_false] at equation
    repeat' first | split at equation | contradiction
    all_goals
      apply advance_core covered equation
      refine ⟨bodyCore,?_⟩
      intro label member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨by simp [Forall],tail⟩
      · exact labels label member
  | loop bt body bodyCore =>
    simp only [instruction,astep,enterLabel,ite_true] at equation
    repeat' first | split at equation | contradiction
    all_goals
      apply advance_core covered equation
      refine ⟨bodyCore,?_⟩
      intro label member
      rcases List.mem_cons.mp member with rfl | member
      · refine ⟨?_,tail⟩
        intro i member
        have same := List.mem_singleton.mp member
        subst i
        exact .loop bt body bodyCore
      · exact labels label member
  | ifelse bt yes no yesCore noCore =>
    simp only [instruction,astep] at equation
    repeat' first | split at equation | contradiction
    all_goals
      apply advance_core covered equation
      refine ⟨?_,labels⟩
      intro i member
      rcases List.mem_cons.mp member with rfl | member
      · apply CoreInstr.block
        first | assumption | split <;> assumption
      · exact tail i member

/-- The source grammar and retained function-body coverage survive every
successful Core transition; no immutable-store assumption is used. -/
theorem step_core (s next : AState) (typed : ATyped s) (covered : CoreState s)
    (equation : step s = .next next) : CoreState next := by
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
        exact instruction_core source ambient frame rest op after next (body.1 op (by simp)) frameTyped covered equation
      | nil =>
        cases labels with
        | nil => exact returnFrame_core covered equation
        | cons label labels =>
          simp only [step,astep] at equation
          split at equation
          · apply advance_core covered equation
            exact ⟨(body.2 label (by simp)).2,fun outer member => body.2 outer (by simp [member])⟩
          · contradiction

end Exec.Abs.Core
