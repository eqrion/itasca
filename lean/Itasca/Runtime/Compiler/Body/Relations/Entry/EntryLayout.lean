import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlLayout
import Itasca.Runtime.Compiler.Local.Relations.Table.ControlTablePreservation

/-!
Proofs for Runtime / Compiler / Body / Relations / Entry.

This module collects EntryLayout, EntrySignatures.
Each section documents its contracts and consumers.
-/

/-! ## EntryLayout -/

section

open Itasca.Representation

/-!
The compiler and canonical validator use the same word width, even for a polymorphic operand that has no concrete source value.

Main declarations: `stack_words_types` and `Body.ReaderEnterPost.layout`.
-/

namespace Itasca.Compiler
open Aeneas.Std Itasca

/-- The compiler and canonical validator use the same word width, even for a
polymorphic operand that has no concrete source value. -/
theorem stack_words_types (values : List code.StackType) :
    stackWords values = slots (Body.Stack.stackTypes values) := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    cases value <;> simp [stackWords, Body.Stack.stackTypes, slots, compilerStackWidth, width] at ih ⊢ <;> omega

/-- A reader's child frame base identifies exactly the physical source prefix
below its parameters. This comes from the canonical control zipper. -/
theorem _root_.Itasca.Body.ReaderEnterPost.front {data env locals index st out form bt ins outs remaining base}
    {p : Body.Pending data env locals index st}
    (post : Body.ReaderEnterPost p out form bt ins outs remaining base)
    (initial : form.Initial) :
    out.core.ctrls.val = (p.parents ++ [{p.current with vals := remaining}]).map Body.Frames.Saved.ctrl ++
      [(Body.Frames.Saved.fresh base form bt ins outs).ctrl] ∧
    base.val ≤ out.core.vals.val.length ∧
    out.core.vals.val.take base.val = p.parents.flatMap Body.Frames.Saved.vals ++ remaining ∧
    out.core.vals.val = (p.parents.flatMap Body.Frames.Saved.vals ++ remaining) ++ ins.map code.StackType.Val := by
  obtain ⟨C, outer, spine, header, position, typed, controls, blocks, values⟩ := post.opened
  have outerEq : outer = p.parents.flatMap Body.Frames.Saved.vals ++ remaining := by
    simpa [List.flatMap_append] using spine_values spine
  have params : form.params ins = ins := by rcases initial with rfl | rfl | rfl <;> rfl
  have baseEq : base.val = outer.length := position
  have valuesEq : out.core.vals.val = outer ++ ins.map code.StackType.Val := by
    simpa [Body.Frames.Saved.fresh, params] using values
  refine ⟨controls, ?_, ?_, ?_⟩
  · simp [valuesEq, baseEq]
  · rw [valuesEq, baseEq, List.take_left, outerEq]
  · simpa only [outerEq] using valuesEq

/-- Live entry height fits the existing machine word bound because its source
front is a prefix of the already observed operand stack. -/
theorem _root_.Itasca.Body.ReaderEnterPost.layout {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {data env locals index st out form bt ins outs remaining base}
    {p : Body.Pending data env locals index st}
    (post : Body.ReaderEnterPost p out form bt ins outs remaining base)
    (initial : form.Initial) (live : p.current.ctrl.polymorphic_base = false)
    (known : ConcreteStack st.core.vals.val)
    (layout : CompilerLayout compiler (Body.Stack.stackTypes st.core.vals.val)) :
    ∃ front : List valtype,
      Body.Stack.stackTypes st.core.vals.val = front ++ form.args ins ∧
      Body.Stack.stackTypes out.core.vals.val = front ++ ins.map Translation.valueType ∧
      ConcreteStack out.core.vals.val ∧
      base.val ≤ out.core.vals.val.length ∧
      stackWords (out.core.vals.val.take base.val) = slots front ∧
      compiler.function.local_slots.val + stackWords (out.core.vals.val.take base.val) ≤ U32.max := by
  obtain ⟨front, oldTypes, newTypes, newKnown⟩ := post.stacks initial live known
  obtain ⟨controls, baseFits, prefixEq, values⟩ := post.front initial
  have prefixTypes : Body.Stack.stackTypes (p.parents.flatMap Body.Frames.Saved.vals ++ remaining) = front := by
    have same : Body.Stack.stackTypes (p.parents.flatMap Body.Frames.Saved.vals ++ remaining) ++ ins.map Translation.valueType =
        front ++ ins.map Translation.valueType := by
      simpa only [values, Body.Stack.stackTypes, List.map_append, List.map_map, Function.comp_def] using newTypes
    exact List.append_cancel_right same
  have words : stackWords (out.core.vals.val.take base.val) = slots front := by
    rw [prefixEq, stack_words_types, prefixTypes]
  refine ⟨front, oldTypes, newTypes, newKnown, baseFits, words, ?_⟩
  have height := layout.height
  rw [oldTypes, slots_append] at height
  have bound : compiler.height.val ≤ U32.max := by scalar_tac
  rw [words, layout.localSlots]
  omega

end Itasca.Compiler

end

/-! ## EntrySignatures -/

section

open Itasca.Representation

/-!
Concrete block selection agrees with the canonical resolved parameter and result vectors, including indexed multi-value block signatures.

Main declarations: `SignatureAt.resolved` and `SignatureSequence.select`.
-/

namespace Itasca.Compiler
open Aeneas.Std Itasca

/-- Concrete block selection agrees with the canonical resolved parameter and
result vectors, including indexed multi-value block signatures. -/
theorem SignatureAt.resolved {signatures bt signature env ins outs}
    (selected : SignatureAt signatures bt signature)
    (table : SignatureTable signatures (env.types.val.map Translation.Environment.funcType))
    (inputs : Body.resolve env (Body.inputs bt) = some ins)
    (outputs : Body.resolve env (Body.outputs bt) = some outs) :
    SignatureMatches signature (ins.map Translation.valueType) (outs.map Translation.valueType) := by
  cases selected with
  | empty =>
    simp [Body.inputs, Body.outputs, Body.resolve] at inputs outputs
    subst ins outs
    constructor <;> rfl
  | value ty word bound =>
    simp [Body.inputs, Body.outputs, Body.resolve] at inputs outputs
    subst ins outs
    constructor <;> simp [slots, bound]
  | index index signature found =>
    obtain ⟨params, results, lookup, matched⟩ := table index.val signature found
    simp only [List.getElem?_map] at lookup
    cases atType : env.types.val[index.val]? with
    | none => simp [atType] at lookup
    | some ty =>
      simp only [atType, Option.map_some, Option.some.injEq, Translation.Environment.funcType,
        functype.mk_functype.injEq, list.mk_list.injEq] at lookup
      simp [Body.inputs, Body.outputs, Body.resolve, atType] at inputs outputs
      subst ins outs
      simpa only [← lookup.1, ← lookup.2] using matched

theorem SignatureSequence.select {signatures : Slice runtime.compiler.Signature} {env bt ins outs}
    (sequence : SignatureSequence signatures.val env.types.val)
    (inputs : Body.resolve env (Body.inputs bt) = some ins)
    (outputs : Body.resolve env (Body.outputs bt) = some outs) :
    ∃ signature, SignatureAt signatures bt signature ∧
      SignatureMatches signature (ins.map Translation.valueType) (outs.map Translation.valueType) := by
  have selected : ∃ signature, SignatureAt signatures bt signature := by
    cases bt with
    | Empty => exact ⟨_, .empty⟩
    | Value ty =>
      have bound : width (Translation.valueType ty) < 2^32 := by cases ty <;> decide
      exact ⟨_, .value ty (UScalar.ofNatCore _ bound) rfl⟩
    | TypeIndex index =>
      have inBounds : index.val < env.types.val.length := by
        by_contra h
        simp [Body.inputs, Body.resolve, List.getElem?_eq_none (by omega : env.types.val.length ≤ index.val)] at inputs
      have sigBounds : index.val < signatures.val.length := by rw [List.Forall₂.length_eq sequence]; exact inBounds
      exact ⟨signatures.val[index.val], .index index _ (List.getElem?_eq_getElem sigBounds)⟩
  obtain ⟨signature, selected⟩ := selected
  exact ⟨signature, selected, selected.resolved sequence.table inputs outputs⟩

end Itasca.Compiler

end
