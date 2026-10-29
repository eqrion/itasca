import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownStackTransfer
import Itasca.Handler.RawControl
import Itasca.Wasm2.Control.EnterSound
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
open Itasca

theorem concrete_values (types : List types.ValueType) : ConcreteStack (types.map code.StackType.Val) := by
  simp [ConcreteStack]

/-- Closing or switching a frame reconstructs a concrete stack from the saved
outer operands and its resolved signature, even after a polymorphic dead arm. -/
theorem concrete_end_effect {st out : code.BodyState} {parents blocks frame isElse inputs outputs outer}
    (known : ConcreteStack outer)
    (effect : Wasm2.EndEffect st out parents blocks frame isElse inputs outputs outer) :
    ConcreteStack out.core.vals.val := by
  obtain ⟨_, effect⟩ := effect
  cases isElse with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at effect
    rw [effect.2.2]
    split
    · exact known
    · exact concrete_stack_append.mpr ⟨known, concrete_values outputs⟩
  | true =>
    simp only [↓reduceIte] at effect
    rw [effect.2.2]
    exact concrete_stack_append.mpr ⟨known, concrete_values inputs⟩

theorem wasm2_end_concrete (st out : code.BodyState) (env : module.Env) (isElse : Bool)
    (parents : List code.Ctrl) (blocks : List signature.BlockType) (frame : code.Ctrl)
    (bt : signature.BlockType) (inputs outputs : List types.ValueType) (outer segment : List code.StackType)
    (controls : st.core.ctrls.val = parents ++ [frame]) (signatures : st.blocks.val = blocks ++ [bt])
    (aligned : blocks.length = parents.length) (values : st.core.vals.val = outer ++ segment)
    (base : frame.value_stack_base.val = outer.length)
    (inputTypes : Wasm2.resolve env (Wasm2.inputs bt) = some inputs)
    (outputTypes : Wasm2.resolve env (Wasm2.outputs bt) = some outputs)
    (shape : Control.Shape st.core) (known : ConcreteStack outer)
    (accepted : code.end_frame st env isElse = .ok (.Ok (), out)) : ConcreteStack out.core.vals.val := by
  have effect := code.end_frame.sound st env isElse parents blocks frame bt inputs outputs outer segment
    controls signatures aligned values base inputTypes outputTypes shape
  rw [accepted, WP.spec_ok] at effect
  exact concrete_end_effect known (effect rfl).2.2

end Itasca.Runtime.Compiler
