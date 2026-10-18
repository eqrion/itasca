import Exec.Code.Body.Reader.Common.ReaderEnterStacks
import Exec.Code.Local.Relations.Control.ControlLayout
namespace Exec.Code
open Aeneas.Std Itasca

/-- The compiler and canonical validator use the same word width, even for a
polymorphic operand that has no concrete source value. -/
theorem stackWords_types (values : List code.StackType) :
    stackWords values = slots (Sequence.stackTypes values) := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    cases value <;> simp [stackWords, Sequence.stackTypes, slots, compilerStackWidth, width] at ih ⊢ <;> omega

/-- A reader's child frame base identifies exactly the physical source prefix
below its parameters. This comes from the canonical control zipper. -/
theorem ReaderEnterPostWasm2.front {data env locals index st out form bt ins outs remaining base}
    {p : Wasm2.Pending data env locals index st}
    (post : ReaderEnterPostWasm2 p out form bt ins outs remaining base)
    (initial : form.Initial) :
    out.core.ctrls.val = (p.parents ++ [{p.current with vals := remaining}]).map Wasm2.Frames.Saved.ctrl ++
      [(Wasm2.Frames.Saved.fresh base form bt ins outs).ctrl] ∧
    base.val ≤ out.core.vals.val.length ∧
    out.core.vals.val.take base.val = p.parents.flatMap Wasm2.Frames.Saved.vals ++ remaining ∧
    out.core.vals.val = (p.parents.flatMap Wasm2.Frames.Saved.vals ++ remaining) ++ ins.map code.StackType.Val := by
  obtain ⟨C, outer, spine, header, position, typed, controls, blocks, values⟩ := post.opened
  have outerEq : outer = p.parents.flatMap Wasm2.Frames.Saved.vals ++ remaining := by
    simpa [List.flatMap_append] using wasm2_spine_values spine
  have params : form.params ins = ins := by rcases initial with rfl | rfl | rfl <;> rfl
  have baseEq : base.val = outer.length := position
  have valuesEq : out.core.vals.val = outer ++ ins.map code.StackType.Val := by
    simpa [Wasm2.Frames.Saved.fresh, params] using values
  refine ⟨controls, ?_, ?_, ?_⟩
  · simp [valuesEq, baseEq]
  · rw [valuesEq, baseEq, List.take_left, outerEq]
  · simpa only [outerEq] using valuesEq

/-- Live entry height fits the existing machine word bound because its source
front is a prefix of the already observed operand stack. -/
theorem ReaderEnterPostWasm2.layout {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {data env locals index st out form bt ins outs remaining base}
    {p : Wasm2.Pending data env locals index st}
    (post : ReaderEnterPostWasm2 p out form bt ins outs remaining base)
    (initial : form.Initial) (live : p.current.ctrl.polymorphic_base = false)
    (known : ConcreteStack st.core.vals.val)
    (layout : CompilerLayout compiler (Sequence.stackTypes st.core.vals.val)) :
    ∃ front : List valtype,
      Sequence.stackTypes st.core.vals.val = front ++ form.args ins ∧
      Sequence.stackTypes out.core.vals.val = front ++ ins.map Translate.valueType ∧
      ConcreteStack out.core.vals.val ∧
      base.val ≤ out.core.vals.val.length ∧
      stackWords (out.core.vals.val.take base.val) = slots front ∧
      compiler.function.local_slots.val + stackWords (out.core.vals.val.take base.val) ≤ U32.max := by
  obtain ⟨front, oldTypes, newTypes, newKnown⟩ := post.stacks initial live known
  obtain ⟨controls, baseFits, prefixEq, values⟩ := post.front initial
  have prefixTypes : Sequence.stackTypes (p.parents.flatMap Wasm2.Frames.Saved.vals ++ remaining) = front := by
    have same : Sequence.stackTypes (p.parents.flatMap Wasm2.Frames.Saved.vals ++ remaining) ++ ins.map Translate.valueType =
        front ++ ins.map Translate.valueType := by
      simpa only [values, Sequence.stackTypes, List.map_append, List.map_map, Function.comp_def] using newTypes
    exact List.append_cancel_right same
  have words : stackWords (out.core.vals.val.take base.val) = slots front := by
    rw [prefixEq, stackWords_types, prefixTypes]
  refine ⟨front, oldTypes, newTypes, newKnown, baseFits, words, ?_⟩
  have height := layout.height
  rw [oldTypes, slots_append] at height
  have bound : compiler.height.val ≤ U32.max := by scalar_tac
  rw [words, layout.localSlots]
  omega

/-- Wasm 1 entry has no block parameters; its entire post-reader operand vector
is the physical prefix below the fresh control frame. -/
theorem ReaderEnterPostWasm1.front {data env ctx bodyBt st out form bt remaining token}
    {p : Wasm1.Pending data env ctx bodyBt st}
    (post : ReaderEnterPostWasm1 p out form bt remaining token) :
    out.ctrls.val = (p.parents ++ [{p.current with vals := remaining}]).map Wasm1.Frames.Saved.ctrl ++
      [(Wasm1.Frames.Saved.fresh out form bt).ctrl] ∧
    (Wasm1.Frames.Saved.fresh out form bt).ctrl.value_stack_base.val = out.vals.val.length ∧
    out.vals.val = p.parents.flatMap Wasm1.Frames.Saved.vals ++ remaining := by
  obtain ⟨C, outer, spine, header, position, typed, controls, values⟩ := post.opened
  have outerEq : outer = p.parents.flatMap Wasm1.Frames.Saved.vals ++ remaining := by
    simpa [List.flatMap_append] using wasm1_spine_values spine
  have valuesEq : out.vals.val = outer := by simpa [Wasm1.Frames.Saved.fresh] using values
  exact ⟨controls, by simpa only [valuesEq] using position, valuesEq.trans outerEq⟩

theorem ReaderEnterPostWasm1.layout {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {data env ctx bodyBt st out form bt remaining token}
    {p : Wasm1.Pending data env ctx bodyBt st}
    (post : ReaderEnterPostWasm1 p out form bt remaining token)
    (live : p.current.ctrl.polymorphic_base = false) (known : ConcreteStack st.vals.val)
    (layout : CompilerLayout compiler (Sequence.stackTypes st.vals.val)) :
    ∃ front : List valtype,
      Sequence.stackTypes st.vals.val = front ++ form.inputs ∧
      Sequence.stackTypes out.vals.val = front ∧ ConcreteStack out.vals.val ∧
      stackWords (out.vals.val.take (Wasm1.Frames.Saved.fresh out form bt).ctrl.value_stack_base.val) = slots front ∧
      compiler.function.local_slots.val +
        stackWords (out.vals.val.take (Wasm1.Frames.Saved.fresh out form bt).ctrl.value_stack_base.val) ≤ U32.max := by
  obtain ⟨front, oldTypes, newTypes, newKnown⟩ := post.stacks live known
  obtain ⟨controls, position, values⟩ := post.front
  have words : stackWords (out.vals.val.take (Wasm1.Frames.Saved.fresh out form bt).ctrl.value_stack_base.val) = slots front := by
    rw [position, List.take_length, stackWords_types, newTypes]
  refine ⟨front, oldTypes, newTypes, newKnown, words, ?_⟩
  have height := layout.height
  rw [oldTypes, slots_append] at height
  have bound : compiler.height.val ≤ U32.max := by scalar_tac
  rw [words, layout.localSlots]
  omega

end Exec.Code
