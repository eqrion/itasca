import Itasca.Runtime.Abs.Numeric.Effect
import Itasca.Runtime.Abs.StepSafety
import Itasca.Runtime.Abs.Core.Step
import Itasca.Runtime.Abs.Supported.CoreStuck
import Itasca.Runtime.Abs.Core.Pure
import Itasca.Runtime.Abs.Supported.PureCoverage
namespace Itasca.Runtime.Abs.Supported
open Itasca.Runtime.Abs.Core

/-- Successful instructions retain the supported source grammar, including
unchanged defined function bodies after mutable object-content writes. -/
theorem instruction_covered (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (descriptor : CoreHead op)
    (typed : FrameTyped s {f with code := op :: after} [])
    (covered : SupportedState ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩)
    (equation : instruction s ambient f rest op after = .next next) : SupportedState next := by
  have frame := covered.active {f with code := op :: after} (by simp)
  have tail : Forall BinaryInstr after := fun i member => frame.1 i (by simp [member])
  have labels := frame.2
  cases descriptor with
  | pure pure =>
    rw [instruction_slice s ambient f rest _ after pure typed] at equation
    exact slice_instruction_covered s ambient f rest _ after next pure covered equation
  | const ty value => exact advance_covered covered equation ⟨tail,labels⟩
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

/-- The source grammar and retained function-body coverage survive every
successful Core transition; no immutable-store assumption is used. -/
theorem step_covered (s next : AState) (typed : ATyped s) (covered : SupportedState s)
    (equation : step s = .next next) : SupportedState next := by
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
        rcases Abs.BinaryInstr.core_head (body.1 op (by simp)) with head | stuck
        · exact instruction_covered source ambient frame rest op after next head frameTyped covered equation
        · exact nomatch (stuck _ _ _ _ _).symm.trans equation
      | nil =>
        cases labels with
        | nil => exact returnFrame_covered covered equation
        | cons label labels =>
          simp only [step,astep] at equation
          split at equation
          · apply advance_covered covered equation
            exact ⟨(body.2 label (by simp)).2,fun outer member => body.2 outer (by simp [member])⟩
          · contradiction

end Itasca.Runtime.Abs.Supported
