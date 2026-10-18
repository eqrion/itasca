import Exec.Abs.Core.Progress
import Exec.Abs.Sim.Terminal

namespace Exec.Abs.Core
open SpecExt Exec.Spec

/-- Core traps are generated source traps: integer exceptional arithmetic,
explicit unreachable, and scalar memory bounds failures. -/
theorem instruction_trap (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr)
    (covered : CoreInstr op)
    (typed : CoreTyped ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩)
    (equation : instruction s ambient f rest op after = .trap) :
    ∃ n, 0 < n ∧ StepsHN n (decode ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩) []
      ⟨⟨s,ambient⟩,[.TRAP]⟩ := by
  have frameTyped : FrameTyped s {f with code := op :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  cases covered with
  | slice pure =>
    rw [instruction_slice s ambient f rest _ after pure frameTyped] at equation
    rcases instruction_trap_eq s ambient f rest _ after pure equation with rfl | ⟨descriptor,rfl⟩
    · obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frameTyped_wf frameTyped
      have restWf : Forall FrameWf rest := by
        cases typed.typed.frames with | cons _ tail => exact framesTyped_wf tail
      exact unreachable_simulation s ambient f rest after typed.typed.store typed.typed.ambient
        frameWf labelsWf valuesWf (fun i member => codeWf i (by simp [member])) restWf
    · exact Numeric.astep_trap_simulation s ambient f rest after descriptor typed.typed equation
  | constant ty value => simp [instruction,advance] at equation
  | select =>
    obtain ⟨next,actual,_,_⟩ := select_progress s ambient f rest after typed
    change select _ _ _ _ = .trap at equation
    rw [actual] at equation
    contradiction
  | global_get index =>
    cases index with
    | mk_uN index =>
      obtain ⟨next,actual,_,_⟩ := globalGet_progress s ambient f rest index after typed
      change globalGet _ _ _ _ _ = .trap at equation
      rw [actual] at equation
      contradiction
  | global_set index =>
    cases index with
    | mk_uN index =>
      obtain ⟨next,actual,_,_,_⟩ := globalSet_progress s ambient f rest index after typed
      change globalSet _ _ _ _ _ = .trap at equation
      rw [actual] at equation
      contradiction
  | load descriptor argument =>
    rw [instruction_load] at equation
    rcases load_progress s ambient f rest after descriptor argument typed with ⟨next,actual,_,_⟩ | ⟨actual,source⟩
    · rw [actual] at equation
      contradiction
    · exact source
  | store descriptor argument =>
    rw [instruction_store] at equation
    rcases store_progress s ambient f rest after descriptor argument typed with ⟨next,actual,_,_,_⟩ | ⟨actual,source⟩
    · rw [actual] at equation
      contradiction
    · exact source
  | block bt body _ =>
    simp only [instruction,astep,enterLabel,advance] at equation
    repeat' first | contradiction | split at equation
  | loop bt body _ =>
    simp only [instruction,astep,enterLabel,advance] at equation
    repeat' first | contradiction | split at equation
  | ifelse bt yes no _ _ =>
    simp only [instruction,astep,advance] at equation
    repeat' first | contradiction | split at equation

theorem step_trap (s : AState) (typed : CoreTyped s) (covered : CoreState s)
    (equation : step s = .trap) :
    ∃ n, 0 < n ∧ StepsHN n (decode s) [] ⟨⟨s.store,s.ambient⟩,[.TRAP]⟩ := by
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
      | cons op after => exact instruction_trap source ambient frame rest op after (body op (by simp)) typed equation
      | nil =>
        simp only [step,astep,returnFrame,advance] at equation
        repeat' first | contradiction | split at equation

theorem instruction_not_done (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (values : List val) :
    instruction s ambient f rest op after ≠ .done values := by
  intro equation
  simp only [instruction] at equation
  repeat' first | contradiction | split at equation
  all_goals
    simp only [astep,select,globalGet,globalSet,load,store,advance,returnFrame,branch,enterLabel,call,
      Numeric.transition,Numeric.finish] at equation
    repeat' first | contradiction | split at equation

theorem done_simulation (s : AState) (values : List val) (equation : step s = .done values) :
    decode s = ⟨⟨s.store,s.ambient⟩,vals values⟩ := by
  rcases s with ⟨source,ambient,frames,results⟩
  cases frames with
  | nil =>
    simp only [step,AResult.done.injEq] at equation
    subst results
    rfl
  | cons frame rest =>
    cases frame with
    | mk address resultTypes locals module labels code operands =>
      let frame : AFrame := ⟨address,resultTypes,locals,module,labels,code,operands⟩
      cases code with
      | cons op after =>
        exact False.elim (instruction_not_done source ambient frame rest op after values equation)
      | nil =>
        simp only [step,astep,returnFrame,advance] at equation
        repeat' first | contradiction | split at equation

end Exec.Abs.Core
