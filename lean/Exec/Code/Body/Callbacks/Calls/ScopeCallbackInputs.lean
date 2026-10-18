import Exec.Code.Body.Relations.Common.EntryLayout
import Exec.Code.Body.Relations.Common.EntrySignatures
namespace Exec.Code
open Aeneas.Std Itasca

/-- The canonical Wasm 2 reader and captured type table supply the physical
premises consumed by all live BLOCK, LOOP, and IF callback wrappers. -/
theorem ReaderEnterPostWasm2.callback_inputs {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {data env locals index st out form bt ins outs remaining base}
    {p : Wasm2.Pending data env locals index st}
    (post : ReaderEnterPostWasm2 p out form bt ins outs remaining base)
    (initial : form.Initial) (live : p.current.ctrl.polymorphic_base = false)
    (known : ConcreteStack st.core.vals.val)
    (layout : CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (signatures : SignatureSequence compiler.signatures.val env.types.val) :
    ∃ front signature,
      Sequence.stackTypes st.core.vals.val = front ++ form.args ins ∧
      Sequence.stackTypes out.core.vals.val = front ++ ins.map Translate.valueType ∧
      ConcreteStack out.core.vals.val ∧
      SignatureAt compiler.signatures bt signature ∧
      SignatureMatches signature (ins.map Translate.valueType) (outs.map Translate.valueType) ∧
      out.core.ctrls.val = (p.parents ++ [{p.current with vals := remaining}]).map Wasm2.Frames.Saved.ctrl ++
        [(Wasm2.Frames.Saved.fresh base form bt ins outs).ctrl] ∧
      base.val ≤ out.core.vals.val.length ∧
      stackWords (out.core.vals.val.take base.val) = slots front ∧
      compiler.function.local_slots.val + stackWords (out.core.vals.val.take base.val) ≤ U32.max := by
  obtain ⟨front, before, after, concrete, fits, words, height⟩ := post.layout initial live known layout
  obtain ⟨signature, selected, matched⟩ := signatures.select post.inputs post.outputs
  exact ⟨front, signature, before, after, concrete, selected, matched, (post.front initial).1, fits, words, height⟩

/-- Wasm 1 uses the same physical callback interface, with an empty parameter
vector and a control base equal to the complete post-reader operand length. -/
theorem ReaderEnterPostWasm1.callback_inputs {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {data env ctx bodyBt st out form bt remaining token}
    {p : Wasm1.Pending data env ctx bodyBt st}
    (post : ReaderEnterPostWasm1 p out form bt remaining token)
    (live : p.current.ctrl.polymorphic_base = false) (known : ConcreteStack st.vals.val)
    (layout : CompilerLayout compiler (Sequence.stackTypes st.vals.val)) :
    ∃ front signature,
      Sequence.stackTypes st.vals.val = front ++ form.inputs ∧
      Sequence.stackTypes out.vals.val = front ∧ ConcreteStack out.vals.val ∧
      SignatureAt compiler.signatures (Control.signature bt) signature ∧
      SignatureMatches signature [] (Control.resultTypes bt) ∧
      out.ctrls.val = (p.parents ++ [{p.current with vals := remaining}]).map Wasm1.Frames.Saved.ctrl ++
        [(Wasm1.Frames.Saved.fresh out form bt).ctrl] ∧
      (Wasm1.Frames.Saved.fresh out form bt).ctrl.value_stack_base.val = out.vals.val.length ∧
      stackWords (out.vals.val.take (Wasm1.Frames.Saved.fresh out form bt).ctrl.value_stack_base.val) = slots front ∧
      compiler.function.local_slots.val +
        stackWords (out.vals.val.take (Wasm1.Frames.Saved.fresh out form bt).ctrl.value_stack_base.val) ≤ U32.max := by
  obtain ⟨front, before, after, concrete, words, height⟩ := post.layout live known layout
  obtain ⟨signature, selected, matched⟩ := wasm1_signature_select compiler.signatures bt
  exact ⟨front, signature, before, after, concrete, selected, matched, post.front.1, post.front.2.1, words, height⟩

end Exec.Code
