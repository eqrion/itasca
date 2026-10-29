import Itasca.Runtime.SourceMachine.Core.Correct

namespace Itasca.Runtime.SourceMachine.Core
open SpecExt Itasca.Runtime.Spec

theorem instruction_extends (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (covered : CoreHead op)
    (typed : CoreTyped ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩)
    (equation : instruction s ambient f rest op after = .next next) : Extend_store s next.store := by
  have frameTyped : FrameTyped s {f with code := op :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  have unchanged (same : next.store = s) : Extend_store s next.store := by
    rw [same]
    exact extend_store_refl s typed.typed.store
  cases covered with
  | pure pure =>
    rw [instruction_slice s ambient f rest _ after pure frameTyped] at equation
    exact unchanged (astep_store equation)
  | const ty value =>
    simp only [instruction,advance,AResult.next.injEq] at equation
    cases equation
    exact unchanged rfl
  | select =>
    apply unchanged
    simp only [instruction,select] at equation
    repeat' first | contradiction | split at equation
    all_goals
      simp only [advance,AResult.next.injEq] at equation
      cases equation
      rfl
  | global_get index =>
    apply unchanged
    cases index
    simp only [instruction,globalGet] at equation
    repeat' first | contradiction | split at equation
    all_goals
      simp only [advance,AResult.next.injEq] at equation
      cases equation
      rfl
  | global_set index =>
    cases index with
    | mk_uN index =>
      obtain ⟨actual,actualEq,_,extension,_⟩ := global_set_progress s ambient f rest index after typed
      change globalSet _ _ _ _ _ = .next next at equation
      rw [actualEq] at equation
      cases equation
      exact extension
  | load descriptor argument =>
    apply unchanged
    rw [instruction_load] at equation
    simp only [load] at equation
    repeat' first | contradiction | split at equation
    all_goals
      simp only [advance,AResult.next.injEq] at equation
      cases equation
      rfl
  | store descriptor argument =>
    rw [instruction_store] at equation
    rcases store_progress s ambient f rest after descriptor argument typed with
      ⟨actual,actualEq,_,extension,_⟩ | ⟨actualEq,_⟩
    · rw [actualEq] at equation
      cases equation
      exact extension
    · rw [actualEq] at equation
      contradiction

end Itasca.Runtime.SourceMachine.Core
