import Exec.Code.Body.Callbacks.Calls.ScopeCallbackInputs
import Exec.Code.Local.Relations.Control.ControlEntrySuccess
namespace Exec.Code
open Aeneas.Std Itasca

/-- Successful dormant Wasm 2 entry supplies all physical signature and
coordinate premises from the canonical reader. No live-stack or height-bound
assumption is imposed on the discarded source body. -/
theorem ReaderEnterPostWasm2.accepted_inputs {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    {data env locals index st out form bt ins outs remaining base}
    {p : Wasm2.Pending data env locals index st}
    (post : ReaderEnterPostWasm2 p out form bt ins outs remaining base)
    (initial : form.Initial)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (accepted : runtime.compiler.control.FunctionCompiler.enter ops before out.core form.kind bt = .ok (.Ok (), after)) :
    ∃ signature,
      SignatureAt before.signatures bt signature ∧
      SignatureMatches signature (ins.map Translate.valueType) (outs.map Translate.valueType) ∧
      out.core.ctrls.val = (p.parents ++ [{p.current with vals := remaining}]).map Wasm2.Frames.Saved.ctrl ++
        [(Wasm2.Frames.Saved.fresh base form bt ins outs).ctrl] ∧
      base.val ≤ out.core.vals.val.length ∧
      before.function.local_slots.val + stackWords (out.core.vals.val.take base.val) ≤ U32.max ∧
      before.function.body_start.val + before.next_source.val ≤ Usize.max := by
  obtain ⟨signature, selected, matched⟩ := signatures.select post.inputs post.outputs
  obtain ⟨controls, fits, _, _⟩ := post.front initial
  have coordinates := control_entry_coordinates ops before after out.core
    (Wasm2.Frames.Saved.fresh base form bt ins outs).ctrl
    ((p.parents ++ [{p.current with vals := remaining}]).map Wasm2.Frames.Saved.ctrl)
    form.kind bt controls fits accepted
  exact ⟨signature, selected, matched, controls, fits, coordinates⟩

/-- Wasm 1 has no indexed block signatures; accepted entry similarly supplies
its arithmetic bounds without requiring concrete dead operands. -/
theorem ReaderEnterPostWasm1.accepted_inputs {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    {data env ctx bodyBt st out form bt remaining token}
    {p : Wasm1.Pending data env ctx bodyBt st}
    (post : ReaderEnterPostWasm1 p out form bt remaining token)
    (accepted : runtime.compiler.control.FunctionCompiler.enter ops before out form.kind (Control.signature bt) = .ok (.Ok (), after)) :
    ∃ signature,
      SignatureAt before.signatures (Control.signature bt) signature ∧
      SignatureMatches signature [] (Control.resultTypes bt) ∧
      out.ctrls.val = (p.parents ++ [{p.current with vals := remaining}]).map Wasm1.Frames.Saved.ctrl ++
        [(Wasm1.Frames.Saved.fresh out form bt).ctrl] ∧
      (Wasm1.Frames.Saved.fresh out form bt).ctrl.value_stack_base.val = out.vals.val.length ∧
      before.function.local_slots.val +
        stackWords (out.vals.val.take (Wasm1.Frames.Saved.fresh out form bt).ctrl.value_stack_base.val) ≤ U32.max ∧
      before.function.body_start.val + before.next_source.val ≤ Usize.max := by
  obtain ⟨signature, selected, matched⟩ := wasm1_signature_select before.signatures bt
  obtain ⟨controls, position, _⟩ := post.front
  have coordinates := control_entry_coordinates ops before after out
    (Wasm1.Frames.Saved.fresh out form bt).ctrl
    ((p.parents ++ [{p.current with vals := remaining}]).map Wasm1.Frames.Saved.ctrl)
    form.kind (Control.signature bt) controls (by rw [position]) accepted
  exact ⟨signature, selected, matched, controls, position, coordinates⟩

end Exec.Code
