import Itasca.Runtime.Code.Body.Reader.Common.ReaderWasm2
import Itasca.Runtime.Code.Body.Reader.Common.ReaderStacks
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem ReaderPostWasm2.values {data env locals index st out instruction poly values}
    {p : Wasm2.Pending data env .Wasm2 locals index st} (post : ReaderPostWasm2 p out instruction poly values) :
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
    ∃ (front : List valtype) (types : List Itasca.types.ValueType), Sequence.stackTypes before = front ++ inputs.map Translate.valueType ∧
      after = types.map code.StackType.Val ∧
      types.map Translate.valueType = front ++ [Translate.valueType output] := by
  have both : ConcreteStack outer ∧ ConcreteStack segment := concreteStack_append.mp (old ▸ known)
  obtain ⟨front, oldTypes, newTypes, resultKnown⟩ := numeric_effect_types both.2 effect
  have afterKnown : ConcreteStack after := new ▸ concreteStack_append.mpr ⟨both.1, resultKnown⟩
  obtain ⟨types, concrete⟩ := (concreteStack_iff after).mp afterKnown
  refine ⟨Sequence.stackTypes outer ++ front, types, ?_, concrete, ?_⟩
  · simp only [old, Sequence.stackTypes, List.map_append] at oldTypes ⊢
    simpa only [List.append_assoc, Sequence.stackTypes] using congrArg (Sequence.stackTypes outer ++ ·) oldTypes
  · have whole := congrArg Sequence.stackTypes concrete
    simp only [Sequence.stackTypes, List.map_map, Function.comp_def] at whole
    rw [← whole]
    change Sequence.stackTypes after = _
    simp only [new, Sequence.stackTypes, List.map_append] at newTypes ⊢
    simpa only [List.append_assoc, Sequence.stackTypes] using congrArg (Sequence.stackTypes outer ++ ·) newTypes

end Itasca.Runtime.Code
