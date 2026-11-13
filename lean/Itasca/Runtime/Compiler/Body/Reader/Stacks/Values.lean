import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownStackTransfer
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post

/-!
Sections, each formerly its own module: Stacks, Values.
-/

/-! ## Stacks -/

section

/-!
A live concrete stack has exactly one declarative interpretation.

Main declarations: `realized_concrete_types` and `numeric_effect_types`. A direct consumer is `Compiler.Body.Reader.Control.ElseExitSlots`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- A live concrete stack has exactly one declarative interpretation. -/
theorem realized_concrete_types {values : List code.StackType} {types : List valtype}
    (known : ConcreteStack values) (realized : Sequence.Realizes false values types) :
    types = Sequence.stackTypes values := by
  obtain ⟨front, suffix, empty, related, rfl⟩ := realized
  rw [empty rfl, List.nil_append]
  induction related with
  | nil => rfl
  | @cons value ty rest types accepted related ih =>
    have tail : ConcreteStack rest := fun v member => known v (by simp [member])
    have head := known value (by simp)
    cases value with
    | Bot => exact False.elim (head rfl)
    | Val value =>
      change ty = Translate.valueType value at accepted
      simp only [Sequence.stackTypes, List.map_cons, accepted]
      exact congrArg (List.cons _) (ih tail)

/-- Successful numeric readers expose the exact concrete input suffix and the
corresponding output stack, including source framing below the operands. -/
theorem numeric_effect_types {before after : List code.StackType} {inputs output}
    (known : ConcreteStack before)
    (effect : StackSemantics.NumericEffect false before inputs output after) :
    ∃ front, Sequence.stackTypes before = front ++ inputs.map Translate.valueType ∧
      Sequence.stackTypes after = front ++ [Translate.valueType output] ∧ ConcreteStack after := by
  have afterKnown := concrete_numeric_effect known effect
  obtain ⟨rest, rfl, transfer⟩ := effect
  have beforeTypes := realized_concrete_types known (transfer _ (Sequence.realizes_default false rest))
  exact ⟨Sequence.stackTypes rest, beforeTypes.symm, by simp [Sequence.stackTypes], afterKnown⟩

end Itasca.Runtime.Compiler

end

/-! ## Values -/

section

/-!
Concrete operand values and their types after reader execution.

Main declarations: `Wasm2.ReaderPost.values` and `numeric_full_stack_types`. A direct consumer is `Compiler.Body.Reader.Acceptance.SourceBoundNumericExtensionAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem _root_.Itasca.Wasm2.ReaderPost.values {data env locals index st out instruction poly values}
    {p : Wasm2.Pending data env locals index st} (post : Wasm2.ReaderPost p out instruction poly values) :
    st.core.vals.val = p.parents.flatMap Wasm2.Frames.Saved.vals ++ p.current.vals ∧
    out.vals.val = p.parents.flatMap Wasm2.Frames.Saved.vals ++ values := by
  obtain ⟨_, outer, spine, _, _, _, _, _, old⟩ := p.opened
  obtain ⟨_, outer', spine', _, _, _, _, _, new⟩ := post.opened
  exact ⟨by simpa only [wasm2_spine_values spine] using old,
    by simpa only [wasm2_spine_values spine', Wasm2.Frames.Saved.advance] using new⟩

/-- A numeric reader's live current segment determines the complete physical
stack before and after the instruction, including all suspended source prefixes. -/
theorem numeric_full_stack_types {before after outer segment result : List code.StackType} {inputs output}
    (known : ConcreteStack before) (old : before = outer ++ segment) (new : after = outer ++ result)
    (effect : StackSemantics.NumericEffect false segment inputs output result) :
    ∃ (front : List valtype) (types : List Itasca.wasm_types.ValueType), Sequence.stackTypes before = front ++ inputs.map Translate.valueType ∧
      after = types.map code.StackType.Val ∧
      types.map Translate.valueType = front ++ [Translate.valueType output] := by
  have both : ConcreteStack outer ∧ ConcreteStack segment := concrete_stack_append.mp (old ▸ known)
  obtain ⟨front, oldTypes, newTypes, resultKnown⟩ := numeric_effect_types both.2 effect
  have afterKnown : ConcreteStack after := new ▸ concrete_stack_append.mpr ⟨both.1, resultKnown⟩
  obtain ⟨types, concrete⟩ := (concrete_stack_iff after).mp afterKnown
  refine ⟨Sequence.stackTypes outer ++ front, types, ?_, concrete, ?_⟩
  · simp only [old, Sequence.stackTypes, List.map_append] at oldTypes ⊢
    simpa only [List.append_assoc, Sequence.stackTypes] using congrArg (Sequence.stackTypes outer ++ ·) oldTypes
  · have whole := congrArg Sequence.stackTypes concrete
    simp only [Sequence.stackTypes, List.map_map, Function.comp_def] at whole
    rw [← whole]
    change Sequence.stackTypes after = _
    simp only [new, Sequence.stackTypes, List.map_append] at newTypes ⊢
    simpa only [List.append_assoc, Sequence.stackTypes] using congrArg (Sequence.stackTypes outer ++ ·) newTypes

end Itasca.Runtime.Compiler

end
