import Itasca.Runtime.Compiler.Body.Relations.Entry.EntryLayout

open Itasca.Representation

/-!
# Control-opener callback inputs

The canonical reader and captured type table supply the physical inputs needed by live BLOCK, LOOP and IF callbacks. Entry lowering consumes these derived premises.
-/
namespace Itasca.Compiler
open Aeneas.Std Itasca

/-- The canonical Wasm 2 reader and captured type table supply the physical
premises consumed by all live BLOCK, LOOP, and IF callback wrappers. -/
theorem _root_.Itasca.Body.ReaderEnterPost.callback_inputs {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {data env locals index st out form bt ins outs remaining base}
    {p : Body.Pending data env locals index st}
    (post : Body.ReaderEnterPost p out form bt ins outs remaining base)
    (initial : form.Initial) (live : p.current.ctrl.polymorphic_base = false)
    (known : ConcreteStack st.core.vals.val)
    (layout : CompilerLayout compiler (Body.Stack.stackTypes st.core.vals.val))
    (signatures : SignatureSequence compiler.signatures.val env.types.val) :
    ∃ front signature,
      Body.Stack.stackTypes st.core.vals.val = front ++ form.args ins ∧
      Body.Stack.stackTypes out.core.vals.val = front ++ ins.map Translation.valueType ∧
      ConcreteStack out.core.vals.val ∧
      SignatureAt compiler.signatures bt signature ∧
      SignatureMatches signature (ins.map Translation.valueType) (outs.map Translation.valueType) ∧
      out.core.ctrls.val = (p.parents ++ [{p.current with vals := remaining}]).map Body.Frames.Saved.ctrl ++
        [(Body.Frames.Saved.fresh base form bt ins outs).ctrl] ∧
      base.val ≤ out.core.vals.val.length ∧
      stackWords (out.core.vals.val.take base.val) = slots front ∧
      compiler.function.local_slots.val + stackWords (out.core.vals.val.take base.val) ≤ U32.max := by
  obtain ⟨front, before, after, concrete, fits, words, height⟩ := post.layout initial live known layout
  obtain ⟨signature, selected, matched⟩ := signatures.select post.inputs post.outputs
  exact ⟨front, signature, before, after, concrete, selected, matched, (post.front initial).1, fits, words, height⟩

end Itasca.Compiler
