import Exec.Code.Body.Reader.Control.ReaderBranchInfoWasm1
import Exec.Code.Local.Relations.Calls.BranchCallbackSafety
import Exec.Code.Body.Reader.Common.ReaderSafety
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

private theorem branch_reader_total_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) (conditional : Bool) :
    (if conditional then code.read_br_if st data else code.read_br st data) ⦃ _ => True ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, controls, values, contextWf, labels, returns⟩ :=
    p.opened.context (EnvTranslation.context_wf env ctx)
  have sourceLabels : (Wasm1.Frames.enter C p.current.form p.current.ctrl.block_type).LABELS =
      Control.labels st.ctrls.val := by simpa [EnvTranslation.context] using labels
  cases conditional with
  | false =>
    exact WP.spec_mono (code.read_br.prefix st data (p.parents.map Wasm1.Frames.Saved.ctrl)
      p.current.ctrl outer p.current.vals controls values base _ contextWf p.current.ops typed sourceLabels) (by simp)
  | true =>
    have physicalBase : (Control.base st).val = outer.length := by simp [Control.base,controls,base]
    have poly : Control.polymorphic st = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic,controls]
    exact WP.spec_mono (code.read_br_if.prefix st data outer p.current.vals values physicalBase
      (by have := p.val_capacity; omega) _ contextWf p.current.ops (by simpa [poly] using typed) sourceLabels) (by simp)

theorem compiler_branch_reader_wasm1_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    {data env ctx bt state} (p : Wasm1.Pending data env ctx bt state) (conditional : Bool)
    (frames : compiler.frames.val.length = state.ctrls.val.length)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (pcBound : compiler.function.code.val.length+3 < 2^32)
    (codeFits : compiler.function.code.val.length+3 ≤ Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length+3 ≤ Usize.max)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max) :
    CoreVisitor.run (if conditional then code.read_br_if state data else code.read_br state data)
      (fun c s pair => if conditional then
        (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_br_if c s pair.1 (Control.resultView pair.2)
        else (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_br c s pair.1 (Control.resultView pair.2)) compiler ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  apply reader_run_reached _ _ compiler (fun s c => ObservedStack c s.vals.val)
  · exact branch_reader_total_wasm1 p conditional
  · intro out pair read
    obtain ⟨depth,resultBt⟩ := pair
    obtain ⟨middle,target,labelRead,_⟩ := reader_branch_label_wasm1 state out data conditional depth resultBt read
    have labelEffect := code.read_label.spec state data
    rw [labelRead,WP.spec_ok] at labelEffect
    have bound : depth.val < compiler.frames.val.length := by
      have found := labelEffect.2.2.2.1
      omega
    cases conditional with
    | false =>
      exact compiler_br_callback_total ops law compiler out depth (Control.resultView resultBt)
        bound fixups (by omega) (by omega) coordinate
    | true =>
      exact compiler_br_if_callback_total ops law compiler out depth (Control.resultView resultBt)
        bound fixups pcBound codeFits sourceFits coordinate
end Exec.Code
