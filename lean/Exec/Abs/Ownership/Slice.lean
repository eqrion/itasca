import Exec.Abs.Ownership.Numeric
import Exec.Abs.Preservation
namespace Exec.Abs.Ownership
open SpecExt Exec.Spec

theorem instruction_ownership (bound : Bounds) (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState) (results : List val)
    (allowed : SliceInstr op) (frame : FrameOwned bound f)
    (frames : ∀ item ∈ rest, FrameOwned bound item)
    (resultBound : ValuesOwned bound results)
    (step : astep ⟨s, ambient, {f with code := op :: after} :: rest, results⟩ = .next next) :
    StateOwned bound next := by
  cases allowed with
  | call index => cases index; exact ownership_call frame frames resultBound step
  | ret => exact ownership_return frame frames resultBound step
  | br depth => cases depth; exact ownership_branch frame frames resultBound step
  | block ty body valid => exact ownership_enter frame frames resultBound step
  | loop ty body valid => exact ownership_enter frame frames resultBound step
  | numeric descriptor =>
    cases descriptor
    all_goals
      have localsBound := frame.1
      have valuesOwned := frame.2
      simp only [Numeric.Instruction.source, Numeric.Conversion.source, Numeric.decodeInstruction, astep, integerBinary, if_pos rfl, reduceCtorEq, ite_true, ite_false] at step
      repeat' first
        | solve | exact transition_ownership resultBound frame frames step
        | split at step
        | contradiction
      all_goals
        apply ownership_advance (step := step) resultBound ?_ frames
        constructor
        · first
          | exact localsBound
          | apply ValuesOwned.set localsBound; aesop (add safe forward ValuesOwned.pop)
        · first
          | solve | aesop (add safe forward ValuesOwned.pop)
          | apply valuesOwned_append.mpr; constructor
            · aesop (add safe forward ValuesOwned.pop)
            · apply valuesOwned_cons.mpr; constructor
              · first
                | trivial
                | solve | aesop (add safe forward ValuesOwned.pop)
                | apply localsBound; apply List.mem_of_getElem?; assumption
              · exact valuesOwned_nil _
  | _ =>
    have localsBound := frame.1
    have valuesOwned := frame.2
    simp only [astep, integerBinary, if_pos rfl, reduceCtorEq, ite_true, ite_false] at step
    repeat' first | split at step | contradiction
    all_goals
      apply ownership_advance (step := step) resultBound ?_ frames
      constructor
      · first
        | exact localsBound
        | apply ValuesOwned.set localsBound; aesop (add safe forward ValuesOwned.pop)
      · first
        | solve | aesop (add safe forward ValuesOwned.pop)
        | apply valuesOwned_append.mpr; constructor
          · aesop (add safe forward ValuesOwned.pop)
          · apply valuesOwned_cons.mpr; constructor
            · first
              | trivial
              | solve | aesop (add safe forward ValuesOwned.pop)
              | apply localsBound; apply List.mem_of_getElem?; assumption
            · exact valuesOwned_nil _

theorem astep_ownership (s next : AState) (bound : Bounds)
    (slice : SliceState s) (bounded : StateOwned bound s)
    (step : astep s = .next next) : StateOwned bound next := by
  rcases s with ⟨store, ambient, frames, results⟩
  cases frames with
  | nil => simp [astep] at step
  | cons frame rest =>
    have headBound := bounded.2 frame (by simp)
    have restBound : ∀ item ∈ rest, FrameOwned bound item := fun item member => bounded.2 item (by simp [member])
    have allowed := (slice.active frame (by simp)).1
    cases frame with
    | mk address types locals module labels code values =>
      cases code with
      | nil =>
        cases labels with
        | nil => exact ownership_return headBound restBound bounded.1 step
        | cons label labels =>
          simp only [astep] at step
          split at step
          · apply ownership_advance (step := step) bounded.1 ?_ restBound
            exact headBound
          · contradiction
      | cons op after =>
        exact instruction_ownership bound store ambient
          ⟨address, types, locals, module, labels, [], values⟩ rest op after next results
          (allowed op (by simp)) headBound restBound bounded.1 step


end Exec.Abs.Ownership
