import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownStackTransfer
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post

/-!
# Stack Values

Reader stack observations determine the concrete values available to compiler callbacks. These facts transport typed stack information through replay.
-/

/-! ## Stacks -/

section

/-!
A live concrete stack has exactly one declarative interpretation.

Main declarations: `realized_concrete_types` and `numeric_effect_types`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- A live concrete stack has exactly one declarative interpretation. -/
theorem realized_concrete_types {values : List code.StackType} {types : List valtype}
    (known : ConcreteStack values) (realized : Body.Stack.Realizes false values types) :
    types = Body.Stack.stackTypes values := by
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
      change ty = Translation.valueType value at accepted
      simp only [Body.Stack.stackTypes, List.map_cons, accepted]
      exact congrArg (List.cons _) (ih tail)

/-- Successful numeric readers expose the exact concrete input suffix and the
corresponding output stack, including source framing below the operands. -/
theorem numeric_effect_types {before after : List code.StackType} {inputs output}
    (known : ConcreteStack before)
    (effect : Body.Stack.Semantics.NumericEffect false before inputs output after) :
    ∃ front, Body.Stack.stackTypes before = front ++ inputs.map Translation.valueType ∧
      Body.Stack.stackTypes after = front ++ [Translation.valueType output] ∧ ConcreteStack after := by
  have afterKnown := concrete_numeric_effect known effect
  obtain ⟨rest, rfl, transfer⟩ := effect
  have beforeTypes := realized_concrete_types known (transfer _ (Body.Stack.realizes_default false rest))
  exact ⟨Body.Stack.stackTypes rest, beforeTypes.symm, by simp [Body.Stack.stackTypes], afterKnown⟩

end Itasca.Compiler

end

/-! ## Values -/

section

/-!
Concrete operand values and their types after reader execution.

Main declarations: `Body.ReaderPost.values` and `numeric_full_stack_types`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem _root_.Itasca.Body.ReaderPost.values {data env locals index st out instruction poly values}
    {p : Body.Pending data env locals index st} (post : Body.ReaderPost p out instruction poly values) :
    st.core.vals.val = p.parents.flatMap Body.Frames.Saved.vals ++ p.current.vals ∧
    out.vals.val = p.parents.flatMap Body.Frames.Saved.vals ++ values := by
  obtain ⟨_, outer, spine, _, _, _, _, _, old⟩ := p.opened
  obtain ⟨_, outer', spine', _, _, _, _, _, new⟩ := post.opened
  exact ⟨by simpa only [spine_values spine] using old,
    by simpa only [spine_values spine', Body.Frames.Saved.advance] using new⟩

/-- A numeric reader's live current segment determines the complete physical
stack before and after the instruction, including all suspended source prefixes. -/
theorem numeric_full_stack_types {before after outer segment result : List code.StackType} {inputs output}
    (known : ConcreteStack before) (old : before = outer ++ segment) (new : after = outer ++ result)
    (effect : Body.Stack.Semantics.NumericEffect false segment inputs output result) :
    ∃ (front : List valtype) (types : List Itasca.wasm_types.ValueType), Body.Stack.stackTypes before = front ++ inputs.map Translation.valueType ∧
      after = types.map code.StackType.Val ∧
      types.map Translation.valueType = front ++ [Translation.valueType output] := by
  have both : ConcreteStack outer ∧ ConcreteStack segment := concrete_stack_append.mp (old ▸ known)
  obtain ⟨front, oldTypes, newTypes, resultKnown⟩ := numeric_effect_types both.2 effect
  have afterKnown : ConcreteStack after := new ▸ concrete_stack_append.mpr ⟨both.1, resultKnown⟩
  obtain ⟨types, concrete⟩ := (concrete_stack_iff after).mp afterKnown
  refine ⟨Body.Stack.stackTypes outer ++ front, types, ?_, concrete, ?_⟩
  · simp only [old, Body.Stack.stackTypes, List.map_append] at oldTypes ⊢
    simpa only [List.append_assoc, Body.Stack.stackTypes] using congrArg (Body.Stack.stackTypes outer ++ ·) oldTypes
  · have whole := congrArg Body.Stack.stackTypes concrete
    simp only [Body.Stack.stackTypes, List.map_map, Function.comp_def] at whole
    rw [← whole]
    change Body.Stack.stackTypes after = _
    simp only [new, Body.Stack.stackTypes, List.map_append] at newTypes ⊢
    simpa only [List.append_assoc, Body.Stack.stackTypes] using congrArg (Body.Stack.stackTypes outer ++ ·) newTypes

end Itasca.Compiler

end
