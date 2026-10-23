import Exec.Code.Body.Reader.Common.ReaderEnterPrefix
import Exec.Code.Body.Relations.Common.EntrySignatures
import Exec.Code.Local.Callbacks.Common.EnterSafety
import Exec.Code.Body.Reader.Common.ReaderBodySafety
import Exec.Code.Local.Callbacks.Calls.CallbackBounds
import Itasca.Wasm2.Visitor.Total
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

theorem reader_enter_signature_wasm2 {data env locals index st out bt} {form : Frames.Form}
    (p : Wasm2.Pending data env .Wasm2 locals index st) (initial : form.Initial)
    (accepted : code.enter_info st data env .Wasm2 form.kind = .ok (.Ok bt, out)) :
    ∃ ins outs, resolve env (inputs bt) = some ins ∧ resolve env (outputs bt) = some outs := by
  have erased : code.enter st data env .Wasm2 form.kind = .ok (.Ok (), out) := by
    simp [code.enter, accepted, core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨C, outer, spine, header, parentBase, typed, ctrls, blocks, vals⟩ := p.opened
  have capacity : st.blocks.val.length < Usize.max := by
    have := p.ctrls; have := p.inbounds; have := p.size; have := limits.MAX_FUNCTION_BYTES.room
    omega
  have effect := code.enter.sound st data env .Wasm2 form initial outer p.current.vals vals
    (by simp [Control.base, ctrls, parentBase]) p.opened.shape.core capacity
  rw [erased, WP.spec_ok] at effect
  obtain ⟨sourceBt, ins, outs, decoded, _, inputs, outputs, _⟩ := effect rfl
  have info := code.enter_info.bytes st data env .Wasm2 form.kind p.opened.shape.core capacity
  rw [accepted, WP.spec_ok] at info
  obtain ⟨rfl, _⟩ := (info bt rfl).unique decoded
  exact ⟨ins,outs,inputs,outputs⟩

theorem EntryPrefix.height_bound {A} {compiler : runtime.compiler.FunctionCompiler A}
    {before after : code.OpIterState}
    (kept : EntryPrefix before after) (observed : ObservedStack compiler before.vals.val) :
    ∃ prior ctrl, after.ctrls.val = prior ++ [ctrl] ∧
      ctrl.value_stack_base.val ≤ after.vals.val.length ∧
      compiler.function.local_slots.val + stackWords (after.vals.val.take ctrl.value_stack_base.val) ≤ U32.max := by
  obtain ⟨prior,ctrl,controls,bound,suffix,eq⟩ := kept
  refine ⟨prior,ctrl,controls,bound,?_⟩
  have limited := observed.prefix_bound (after.vals.val.take ctrl.value_stack_base.val).length
  rw [← eq,List.take_left] at limited
  exact limited

theorem compiler_enter_reader_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    {data env locals index st} (p : Wasm2.Pending data env .Wasm2 locals index st)
    (form : Frames.Form) (initial : form.Initial)
    (signatures : SignatureSequence compiler.signatures.val env.types.val)
    (observed : ObservedStack compiler st.core.vals.val)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max)
    (pcBound : compiler.function.code.val.length+1 < 2^32)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max) :
    CallbackTrace.bodyRun (code.enter_info st data env .Wasm2 form.kind)
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) (enterAction form) compiler ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  have capacity : st.blocks.val.length < Usize.max := by
    have := p.ctrls; have := p.inbounds; have := p.size; have := limits.MAX_FUNCTION_BYTES.room
    omega
  apply reader_body_run_reached _ _ _ compiler (fun s c => ObservedStack c s.core.vals.val)
  · exact WP.spec_mono (code.enter_info.total st data env .Wasm2 form.kind p.opened.shape.core capacity) (by simp)
  · intro out bt read
    obtain ⟨ins,outs,inputs,outputs⟩ := reader_enter_signature_wasm2 p initial read
    obtain ⟨signature,selected,_⟩ := signatures.select inputs outputs
    obtain ⟨prior,ctrl,controls,bound,height⟩ :=
      (reader_enter_prefix_wasm2 p initial read).height_bound observed
    have normal := compiler_enter_total ops law compiler out.core ctrl prior form.kind bt signature
      controls selected bound height coordinate pcBound codeFits sourceFits mapsFit framesFit
      (by rcases initial with rfl | rfl | rfl <;> simp [Frames.Form.kind])
    rcases initial with rfl | rfl | rfl <;> exact normal
end Exec.Code
