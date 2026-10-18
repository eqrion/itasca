import Exec.Code.Local.Relations.Common.KnownStackTransfer
import Itasca.Handler.RawControl
import Itasca.Wasm2.Control.EnterSound
namespace Exec.Code
open Aeneas Aeneas.Std
open Itasca

theorem concrete_values (types : List types.ValueType) : ConcreteStack (types.map code.StackType.Val) := by
  simp [ConcreteStack]

theorem ConcreteStack.take {values : List code.StackType} (known : ConcreteStack values) (count : Nat) :
    ConcreteStack (values.take count) := by
  intro value member
  exact known value (List.mem_of_mem_take member)

/-- A live entry pops only concrete operands and installs concrete block
parameters, preserving the suspended outer operands as well. -/
theorem concrete_enter_effect {st out : code.BodyState} {form bt inputs outputs outer segment}
    (values : st.core.vals.val = outer ++ segment)
    (known : ConcreteStack st.core.vals.val) (live : Control.polymorphic st.core = false)
    (effect : Wasm2.EnterEffect st out form bt inputs outputs outer segment) :
    ConcreteStack out.core.vals.val := by
  obtain ⟨remaining, base, _, _, transfer, _, _, after⟩ := effect
  rw [live] at transfer
  rw [values] at known
  obtain ⟨outerKnown, segmentKnown⟩ := concreteStack_append.mp known
  rw [after]
  exact concreteStack_append.mpr ⟨concreteStack_append.mpr
    ⟨outerKnown, concrete_stack_transfer segmentKnown transfer⟩, concrete_values inputs⟩

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
    · exact concreteStack_append.mpr ⟨known, concrete_values outputs⟩
  | true =>
    simp only [↓reduceIte] at effect
    rw [effect.2.2]
    exact concreteStack_append.mpr ⟨known, concrete_values inputs⟩

theorem wasm2_enter_concrete (st out : code.BodyState) (data : Slice U8) (env : module.Env)
    (form : Wasm2.Frames.Form) (initial : form.Initial) (outer segment : List code.StackType)
    (values : st.core.vals.val = outer ++ segment) (base : (Control.base st.core).val = outer.length)
    (shape : Control.Shape st.core) (capacity : st.blocks.val.length < Usize.max)
    (known : ConcreteStack st.core.vals.val) (live : Control.polymorphic st.core = false)
    (accepted : code.enter st data env form.kind = .ok (.Ok (), out)) : ConcreteStack out.core.vals.val := by
  have effect := code.enter.sound st data env form initial outer segment values base shape capacity
  rw [accepted, WP.spec_ok] at effect
  obtain ⟨bt, inputs, outputs, _, _, _, _, _, effect⟩ := effect rfl
  exact concrete_enter_effect values known live effect

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

theorem wasm1_block_concrete (st out : code.OpIterState) (data : Slice U8) (bt : code.BlockType)
    (capacity : st.ctrls.val.length < Usize.max) (known : ConcreteStack st.vals.val)
    (accepted : code.read_block st data = .ok (.Ok bt, out)) : ConcreteStack out.vals.val := by
  have effect := code.read_block.raw_spec st data capacity
  rw [accepted, WP.spec_ok] at effect
  have same : out.vals = st.vals := (effect bt rfl).2.1
  rw [same]
  exact known

theorem wasm1_loop_concrete (st out : code.OpIterState) (data : Slice U8) (bt : code.BlockType)
    (capacity : st.ctrls.val.length < Usize.max) (known : ConcreteStack st.vals.val)
    (accepted : code.read_loop st data = .ok (.Ok bt, out)) : ConcreteStack out.vals.val := by
  have effect := code.read_loop.raw_spec st data capacity
  rw [accepted, WP.spec_ok] at effect
  have same : out.vals = st.vals := (effect bt rfl).2.1
  rw [same]
  exact known

theorem wasm1_if_concrete (st out : code.OpIterState) (data : Slice U8) (bt : code.BlockType)
    (outer segment : List code.StackType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length) (capacity : st.ctrls.val.length < Usize.max)
    (known : ConcreteStack st.vals.val) (live : Control.polymorphic st = false)
    (accepted : code.read_if st data = .ok (.Ok bt, out)) : ConcreteStack out.vals.val := by
  have effect := code.read_if.raw_spec st data outer segment values base capacity
  rw [accepted, WP.spec_ok] at effect
  obtain ⟨_, rest, after, _, _, transfer⟩ := effect bt rfl
  rw [live] at transfer
  rw [values] at known
  obtain ⟨outerKnown, segmentKnown⟩ := concreteStack_append.mp known
  rw [after]
  exact concreteStack_append.mpr ⟨outerKnown, concrete_stack_transfer segmentKnown transfer⟩

theorem wasm1_end_concrete (st out : code.OpIterState) (parents : List code.Ctrl) (frame : code.Ctrl)
    (outer segment : List code.StackType) (kind : code.LabelKind) (bt : code.BlockType)
    (controls : st.ctrls.val = parents ++ [frame]) (values : st.vals.val = outer ++ segment)
    (base : frame.value_stack_base.val = outer.length) (capacity : st.vals.val.length + 1 ≤ Usize.max)
    (known : ConcreteStack outer)
    (accepted : code.read_end st = .ok (.Ok (kind, bt), out)) : ConcreteStack out.vals.val := by
  have effect := code.read_end.realizes st parents frame outer segment controls values base capacity
  rw [accepted, WP.spec_ok] at effect
  rw [effect.2.2.2.2.1]
  exact concreteStack_append.mpr ⟨known, concrete_values _⟩

theorem wasm1_else_concrete (st out : code.OpIterState) (parents : List code.Ctrl) (frame : code.Ctrl)
    (outer segment : List code.StackType) (bt : code.BlockType)
    (controls : st.ctrls.val = parents ++ [frame]) (values : st.vals.val = outer ++ segment)
    (base : frame.value_stack_base.val = outer.length) (known : ConcreteStack outer)
    (accepted : code.read_else st = .ok (.Ok bt, out)) : ConcreteStack out.vals.val := by
  have effect := code.read_else.realizes st parents frame outer segment controls values base
  rw [accepted, WP.spec_ok] at effect
  rw [effect.2.2.2.2.1]
  exact known

/-- Unreachable and unconditional transfer discard the current segment; they
retain precisely the known saved operands below the current frame. -/
theorem mark_unreachable_concrete (st out : code.OpIterState) (parents : List code.Ctrl) (frame : code.Ctrl)
    (outer segment : List code.StackType) (controls : st.ctrls.val = parents ++ [frame])
    (values : st.vals.val = outer ++ segment) (base : frame.value_stack_base.val = outer.length)
    (known : ConcreteStack outer) (accepted : code.mark_unreachable st = .ok out) :
    ConcreteStack out.vals.val := by
  have bound : frame.value_stack_base.val ≤ st.vals.val.length := by simp [base, values]
  have effect := code.mark_unreachable.spec st parents frame controls bound
  rw [accepted, WP.spec_ok] at effect
  simpa only [effect.1, values, base, List.take_left] using known
end Exec.Code
