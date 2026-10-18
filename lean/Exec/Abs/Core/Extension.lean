import Exec.Abs.Core.Correct

namespace Exec.Abs.Core
open SpecExt Exec.Spec

theorem instruction_extends (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (covered : CoreInstr op)
    (typed : CoreTyped ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩)
    (equation : instruction s ambient f rest op after = .next next) : Extend_store s next.store := by
  have frameTyped : FrameTyped s {f with code := op :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  have unchanged (same : next.store = s) : Extend_store s next.store := by
    rw [same]
    exact extend_store_refl s typed.typed.store
  cases covered with
  | slice pure =>
    rw [instruction_slice s ambient f rest _ after pure frameTyped] at equation
    exact unchanged (astep_store equation)
  | constant ty value =>
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
      obtain ⟨actual,actualEq,_,extension,_⟩ := globalSet_progress s ambient f rest index after typed
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
  | block bt body _ =>
    exact unchanged (astep_store (s := ⟨s,ambient,{f with code := .BLOCK bt body :: after} :: rest,[]⟩) equation)
  | loop bt body _ =>
    exact unchanged (astep_store (s := ⟨s,ambient,{f with code := .LOOP bt body :: after} :: rest,[]⟩) equation)
  | ifelse bt yes no _ _ =>
    exact unchanged (astep_store (s := ⟨s,ambient,{f with code := .IFELSE bt yes no :: after} :: rest,[]⟩) equation)

/-- The mutable machine preserves issued source objects by the generated store
extension relation at every successful transition. -/
theorem step_extends (s next : AState) (typed : CoreTyped s) (covered : CoreState s)
    (equation : step s = .next next) : Extend_store s.store next.store := by
  rcases s with ⟨source,ambient,frames,results⟩
  cases frames with
  | nil => simp [step] at equation
  | cons frame rest =>
    have noResults := typed.typed.activeResults (by simp)
    change results = [] at noResults
    subst results
    have body := (covered.active frame (by simp)).1
    cases frame with
    | mk address resultTypes locals module labels code values =>
      let frame : AFrame := ⟨address,resultTypes,locals,module,labels,code,values⟩
      cases code with
      | cons op after => exact instruction_extends source ambient frame rest op after next (body op (by simp)) typed equation
      | nil =>
        have same := astep_store (s := ⟨source,ambient,frame :: rest,[]⟩) equation
        rw [same]
        exact extend_store_refl _ typed.typed.store

end Exec.Abs.Core
