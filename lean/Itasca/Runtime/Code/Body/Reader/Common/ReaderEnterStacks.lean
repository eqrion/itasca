import Itasca.Runtime.Code.Body.Reader.Common.ReaderEnterWasm2
import Itasca.Runtime.Code.Body.Reader.Common.ReaderValues
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Live Wasm 2 entry exposes the full physical prefix below its block parameters and condition. -/
theorem ReaderEnterPostWasm2.stacks {data env locals index st out form bt ins outs remaining base}
    {p : Wasm2.Pending data env .Wasm2 locals index st}
    (post : ReaderEnterPostWasm2 p out form bt ins outs remaining base)
    (initial : form.Initial) (live : p.current.ctrl.polymorphic_base = false)
    (known : ConcreteStack st.core.vals.val) :
    ∃ front : List valtype,
      Sequence.stackTypes st.core.vals.val = front ++ form.args ins ∧
      Sequence.stackTypes out.core.vals.val = front ++ ins.map Translate.valueType ∧
      ConcreteStack out.core.vals.val := by
  obtain ⟨C, outer, spine, header, position, typed, controls, blocks, old⟩ := id p.opened
  have old' : st.core.vals.val = p.parents.flatMap Wasm2.Frames.Saved.vals ++ p.current.vals := by
    simpa only [wasm2_spine_values spine] using old
  have knownParts := concreteStack_append.mp (old' ▸ known)
  have transfer := post.popped
  rw [live] at transfer
  have remainingKnown := concrete_stack_transfer knownParts.2 transfer
  have before := realized_concrete_types knownParts.2 (transfer _ (Sequence.realizes_default false remaining))
  obtain ⟨C', outer', spine', header', position', typed', controls', blocks', new⟩ := post.opened
  have params : form.params ins = ins := by rcases initial with rfl | rfl | rfl <;> rfl
  have new' : out.core.vals.val = p.parents.flatMap Wasm2.Frames.Saved.vals ++ remaining ++ ins.map code.StackType.Val := by
    simpa [wasm2_spine_values spine', Wasm2.Frames.Saved.fresh, params, List.flatMap_append] using new
  refine ⟨Sequence.stackTypes (p.parents.flatMap Wasm2.Frames.Saved.vals) ++ Sequence.stackTypes remaining, ?_, ?_, ?_⟩
  · simp only [old', Sequence.stackTypes, List.map_append] at before ⊢
    simpa [List.append_assoc, Sequence.stackTypes] using
      congrArg (Sequence.stackTypes (p.parents.flatMap Wasm2.Frames.Saved.vals) ++ ·) before.symm
  · simp [new', Sequence.stackTypes, List.map_map, Function.comp_def]
  · rw [new']
    exact concreteStack_append.mpr ⟨concreteStack_append.mpr ⟨knownParts.1, remainingKnown⟩,
      (concreteStack_iff _).mpr ⟨ins, rfl⟩⟩

end Itasca.Runtime.Code
