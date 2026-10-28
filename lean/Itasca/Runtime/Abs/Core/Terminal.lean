import Itasca.Runtime.Abs.Core.Pure
import Itasca.Runtime.Abs.Core.MemoryLoad
import Itasca.Runtime.Abs.Core.MemoryStore
import Itasca.Runtime.Abs.Sim.Terminal

namespace Itasca.Runtime.Abs.Core
open SpecExt Itasca.Runtime.Spec

/-- Core traps are generated source traps: integer exceptional arithmetic,
explicit unreachable, and scalar memory bounds failures. -/
theorem instruction_trap (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr)
    (covered : CoreHead op)
    (typed : CoreTyped ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩)
    (equation : instruction s ambient f rest op after = .trap) :
    ∃ n, 0 < n ∧ StepsHN n (decode ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩) []
      ⟨⟨s,ambient⟩,[.TRAP]⟩ := by
  have frameTyped : FrameTyped s {f with code := op :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  cases covered with
  | pure pure =>
    rw [instruction_slice s ambient f rest _ after pure frameTyped] at equation
    rcases instruction_trap_eq s ambient f rest _ after pure equation with rfl | ⟨descriptor,rfl⟩
    · obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frameTyped_wf frameTyped
      have restWf : Forall FrameWf rest := by
        cases typed.typed.frames with | cons _ tail => exact framesTyped_wf tail
      exact unreachable_simulation s ambient f rest after typed.typed.store typed.typed.ambient
        frameWf labelsWf valuesWf (fun i member => codeWf i (by simp [member])) restWf
    · exact Numeric.astep_trap_simulation s ambient f rest after descriptor typed.typed equation
  | const ty value => simp [instruction,advance] at equation
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

end Itasca.Runtime.Abs.Core
