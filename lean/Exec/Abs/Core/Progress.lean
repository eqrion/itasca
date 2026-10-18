import Exec.Abs.Core.Pure
import Exec.Abs.Core.MemoryLoad
import Exec.Abs.Core.MemoryStore

namespace Exec.Abs.Core

/-- Progress is obtained from generated typing inversion for each covered
instruction. A host instruction yields the explicit host boundary, not stuck. -/
theorem instruction_progress (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr)
    (covered : CoreInstr op)
    (typed : CoreTyped ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩) :
    instruction s ambient f rest op after ≠ .stuck := by
  have frameTyped : FrameTyped s {f with code := op :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  cases covered with
  | slice allowed =>
    rw [instruction_slice s ambient f rest _ after allowed frameTyped]
    exact pure_instruction_progress s ambient f rest _ after typed.typed.functions frameTyped allowed
  | constant ty value => simp [instruction,advance]
  | select =>
    obtain ⟨next,equation,_,_⟩ := select_progress s ambient f rest after typed
    change select _ _ _ _ ≠ .stuck
    rw [equation]
    simp only [ne_eq,reduceCtorEq,not_false_eq_true]
  | global_get index =>
    cases index with
    | mk_uN index =>
      obtain ⟨next,equation,_,_⟩ := globalGet_progress s ambient f rest index after typed
      change globalGet _ _ _ _ _ ≠ .stuck
      rw [equation]
      simp only [ne_eq,reduceCtorEq,not_false_eq_true]
  | global_set index =>
    cases index with
    | mk_uN index =>
      obtain ⟨next,equation,_,_,_⟩ := globalSet_progress s ambient f rest index after typed
      change globalSet _ _ _ _ _ ≠ .stuck
      rw [equation]
      simp only [ne_eq,reduceCtorEq,not_false_eq_true]
  | load op argument =>
    rw [instruction_load]
    rcases load_progress s ambient f rest after op argument typed with ⟨next,equation,_,_⟩ | ⟨equation,_⟩
    all_goals rw [equation]; simp only [ne_eq,reduceCtorEq,not_false_eq_true]
  | store op argument =>
    rw [instruction_store]
    rcases store_progress s ambient f rest after op argument typed with ⟨next,equation,_,_,_⟩ | ⟨equation,_⟩
    all_goals rw [equation]; simp only [ne_eq,reduceCtorEq,not_false_eq_true]
  | block bt body _ => exact block_progress s ambient f rest after bt body frameTyped
  | loop bt body _ => exact loop_progress s ambient f rest after bt body frameTyped
  | ifelse bt yes no _ _ => exact if_progress s ambient f rest after bt yes no frameTyped

/-- Every source-typed Core state can take an executable transition, terminate,
trap, or expose its typed host-call boundary. -/
theorem step_progress (s : AState) (typed : CoreTyped s) (covered : CoreState s) :
    step s ≠ .stuck := by
  rcases s with ⟨source,ambient,frames,results⟩
  cases frames with
  | nil => simp [step]
  | cons frame rest =>
    have noResults := typed.typed.activeResults (by simp)
    change results = [] at noResults
    subst results
    have frameTyped : FrameTyped source frame [] := by
      cases typed.typed.frames with | cons head _ => exact head
    have body := (covered.active frame (by simp)).1
    cases frame with
    | mk address resultTypes locals module labels code values =>
      let frame : AFrame := ⟨address,resultTypes,locals,module,labels,code,values⟩
      cases code with
      | nil => exact empty_progress source ambient frame rest frameTyped
      | cons op after =>
        exact instruction_progress source ambient frame rest op after (body op (by simp)) typed

end Exec.Abs.Core
