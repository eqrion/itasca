import Itasca.Runtime.Abs.Ownership.Numeric
import Itasca.Runtime.Abs.Preservation
namespace Itasca.Runtime.Abs.Ownership
open SpecExt Itasca.Runtime.Spec

theorem instruction_ownership (bound : Bounds) (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState) (results : List val)
    (allowed : PureHead op) (frame : FrameOwned bound f)
    (frames : ∀ item ∈ rest, FrameOwned bound item)
    (resultBound : ValuesOwned bound results)
    (step : astep ⟨s, ambient, {f with code := op :: after} :: rest, results⟩ = .next next) :
    StateOwned bound next := by
  cases allowed with
  | call index => cases index; exact ownership_call frame frames resultBound step
  | ret => exact ownership_return frame frames resultBound step
  | br depth => cases depth; exact ownership_branch frame frames resultBound step
  | block ty body => exact ownership_enter frame frames resultBound step
  | loop ty body => exact ownership_enter frame frames resultBound step
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

end Itasca.Runtime.Abs.Ownership
