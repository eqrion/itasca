import Exec.Abs.Numeric.Reference
import Exec.Abs.ReferenceBounds
namespace Exec.Abs
open SpecExt Exec.Spec

theorem instruction_reference_bound (bound : Nat) (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState) (results : List val)
    (allowed : SliceInstr op) (frame : FrameReferencesBound bound f)
    (frames : ∀ item ∈ rest, FrameReferencesBound bound item)
    (resultBound : ValuesBound bound results)
    (step : astep ⟨s, ambient, {f with code := op :: after} :: rest, results⟩ = .next next) :
    StateReferencesBound bound next := by
  cases allowed with
  | call index => cases index; exact references_call frame frames resultBound step
  | ret => exact references_return frame frames resultBound step
  | br depth => cases depth; exact references_branch frame frames resultBound step
  | block ty body valid => exact references_enter frame frames resultBound step
  | loop ty body valid => exact references_enter frame frames resultBound step
  | numeric descriptor =>
    cases descriptor
    all_goals
      have localsBound := frame.1
      have valuesBound := frame.2
      simp only [Numeric.Instruction.source, Numeric.Conversion.source, Numeric.decodeInstruction, astep, integerBinary, if_pos rfl, reduceCtorEq, ite_true, ite_false] at step
      repeat' first
        | solve | exact Numeric.transition_reference_bound resultBound frame frames step
        | split at step
        | contradiction
      all_goals
        apply references_advance (step := step) resultBound ?_ frames
        constructor
        · first
          | exact localsBound
          | apply ValuesBound.set localsBound; aesop (add safe forward ValuesBound.pop)
        · first
          | solve | aesop (add safe forward ValuesBound.pop)
          | apply valuesBound_append.mpr; constructor
            · aesop (add safe forward ValuesBound.pop)
            · apply valuesBound_cons.mpr; constructor
              · first
                | trivial
                | solve | aesop (add safe forward ValuesBound.pop)
                | apply localsBound; apply List.mem_of_getElem?; assumption
              · exact valuesBound_nil _
  | _ =>
    have localsBound := frame.1
    have valuesBound := frame.2
    simp only [astep, integerBinary, if_pos rfl, reduceCtorEq, ite_true, ite_false] at step
    repeat' first | split at step | contradiction
    all_goals
      apply references_advance (step := step) resultBound ?_ frames
      constructor
      · first
        | exact localsBound
        | apply ValuesBound.set localsBound; aesop (add safe forward ValuesBound.pop)
      · first
        | solve | aesop (add safe forward ValuesBound.pop)
        | apply valuesBound_append.mpr; constructor
          · aesop (add safe forward ValuesBound.pop)
          · apply valuesBound_cons.mpr; constructor
            · first
              | trivial
              | solve | aesop (add safe forward ValuesBound.pop)
              | apply localsBound; apply List.mem_of_getElem?; assumption
            · exact valuesBound_nil _

theorem astep_reference_bound (s next : AState) (bound : Nat)
    (slice : SliceState s) (bounded : StateReferencesBound bound s)
    (step : astep s = .next next) : StateReferencesBound bound next := by
  rcases s with ⟨store, ambient, frames, results⟩
  cases frames with
  | nil => simp [astep] at step
  | cons frame rest =>
    have headBound := bounded.2 frame (by simp)
    have restBound : ∀ item ∈ rest, FrameReferencesBound bound item := fun item member => bounded.2 item (by simp [member])
    have allowed := (slice.active frame (by simp)).1
    cases frame with
    | mk address types locals module labels code values =>
      cases code with
      | nil =>
        cases labels with
        | nil => exact references_return headBound restBound bounded.1 step
        | cons label labels =>
          simp only [astep] at step
          split at step
          · apply references_advance (step := step) bounded.1 ?_ restBound
            exact headBound
          · contradiction
      | cons op after =>
        exact instruction_reference_bound bound store ambient
          ⟨address, types, locals, module, labels, [], values⟩ rest op after next results
          (allowed op (by simp)) headBound restBound bounded.1 step

/-- Every finite sequence of actual abstract transitions retains reference bounds. -/
theorem run_reference_bound {n bound : Nat} {s next : AState} {events : List HostEvent}
    (run : Iterations SuccessfulStep n s events next)
    (typed : ATyped s) (slice : SliceState s) (bounded : StateReferencesBound bound s) :
    StateReferencesBound bound next := by
  induction run with
  | refl _ => exact bounded
  | cons transition _ ih =>
    obtain ⟨_, step⟩ := transition
    exact ih (astep_preservation _ _ typed slice step) (astep_slice _ _ typed slice step)
      (astep_reference_bound _ _ bound slice bounded step)
end Exec.Abs
