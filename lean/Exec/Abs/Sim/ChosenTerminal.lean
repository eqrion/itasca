import Exec.Abs.Sim.Terminal
import Exec.Abs.Sim.ChosenUnreachable
import Exec.Abs.Numeric.ChosenTransition
namespace Exec.Abs
open SpecExt Exec.Spec

theorem chosen_typed_trap_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (occurrence : Nat) (s : AState) (typed : ATyped s) (slice : SliceState s)
    (step : astep s = .trap) :
    ∃ n, 0 < n ∧ ChosenStepsN choices occurrence n (decode s) [] ⟨⟨s.store, s.ambient⟩, [.TRAP]⟩ := by
  rcases s with ⟨store, ambient, frames, results⟩
  cases frames with
  | nil => simp [astep] at step
  | cons frame rest =>
    have hresults := typed.activeResults (by simp)
    change results = [] at hresults
    subst results
    have hslice := (slice.active frame (by simp)).1
    have hf : FrameTyped store frame [] := by cases typed.frames with | cons h _ => exact h
    have hr : Forall FrameWf rest := by cases typed.frames with | cons _ h => exact framesTyped_wf h
    obtain ⟨hw, hl, hv, hc⟩ := frameTyped_wf hf
    cases frame with
    | mk addr rts locals m labels code values =>
      let f : AFrame := ⟨addr, rts, locals, m, labels, code, values⟩
      cases code with
      | nil =>
        simp only [astep, returnFrame, advance] at step
        repeat' first | contradiction | split at step
      | cons op after =>
        have hop := instruction_trap_eq store ambient f rest op after (hslice op (by simp)) step
        rcases hop with rfl | ⟨descriptor, rfl⟩
        · exact chosen_unreachable_simulation admissible occurrence store ambient f rest after typed.store typed.ambient hw hl hv
            (fun i hm => hc i (by simp [hm])) hr
        · exact Numeric.chosen_astep_trap_simulation admissible store ambient f rest after descriptor typed step

end Exec.Abs
