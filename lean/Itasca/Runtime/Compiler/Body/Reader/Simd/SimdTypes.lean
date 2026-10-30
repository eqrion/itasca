import Itasca.Wasm2.Simd.Reader
import Itasca.Wasm2.Simd.Sound
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Body.Relations.Stacks.KnownFixedStack
import Itasca.Runtime.Compiler.Body.Reader.Stacks.Values

/-!
Successful live SIMD operand checks expose exact complete source stacks; the physical reader also proves the absence of unknown stack entries.

Main declarations: `reader_simd_fixed_types`. A direct consumer is `Compiler.Body.Reader.Acceptance.SourceBoundTypedSelectAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Successful live SIMD operand checks expose exact complete source stacks;
the physical reader also proves the absence of unknown stack entries. -/
theorem reader_simd_fixed_types {data env locals index st out source values position inputs output}
    {p : Wasm2.Pending data env .Wasm2 locals index st}
    (post : Wasm2.ReaderPost p out source p.current.ctrl.polymorphic_base values)
    (effect : Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals inputs output values)
    (read : Wasm2.Simd.readFixed {st.core with pos := position} inputs output = .ok (.Ok (),out))
    (known : ConcreteStack st.core.vals.val)
    (monomorphic : p.current.ctrl.polymorphic_base = false)
    (capacity : st.core.vals.val.length < Usize.max) :
    ∃ (front : List valtype) (types : List Itasca.wasm_types.ValueType), Sequence.stackTypes st.core.vals.val = front ++ Wasm2.Simd.inputTypes inputs ∧
      out.vals.val = types.map code.StackType.Val ∧
      types.map Translate.valueType = front ++ Wasm2.Simd.outputTypes output := by
  obtain ⟨_,outer,_,_,base,_,ctrls,_,stack⟩ := p.opened
  have physicalBase : (Control.base {st.core with pos := position}).val = outer.length := by
    simp [Control.base,ctrls,base]
  have afterKnown := read_fixed_known {st.core with pos := position} out outer p.current.vals
    inputs output stack physicalBase capacity known read
  obtain ⟨old,new⟩ := post.values
  have currentKnown := (concrete_stack_append.mp (old ▸ known)).2
  rw [monomorphic] at effect
  obtain ⟨front,beforeTypes,afterTypes⟩ := fixed_effect_types currentKnown effect
  obtain ⟨types,concrete⟩ := (concrete_stack_iff out.vals.val).mp afterKnown
  refine ⟨Sequence.stackTypes (p.parents.flatMap Wasm2.Frames.Saved.vals) ++ front,
    types,?_,concrete,?_⟩
  · conv_lhs => rw [old]
    simp only [Sequence.stackTypes,List.map_append]
    change _ ++ Sequence.stackTypes p.current.vals = _
    rw [beforeTypes,List.append_assoc]
  · have decoded : Sequence.stackTypes out.vals.val =
        (Sequence.stackTypes (p.parents.flatMap Wasm2.Frames.Saved.vals) ++ front) ++ Wasm2.Simd.outputTypes output := by
      rw [new]
      simp only [Sequence.stackTypes,List.map_append]
      change _ ++ Sequence.stackTypes values = _
      rw [afterTypes,List.append_assoc]
    simpa only [concrete,Sequence.stackTypes,List.map_map,Function.comp_def] using decoded

end Itasca.Runtime.Compiler
