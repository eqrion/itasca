import Exec.Code.Body.Reader.Common.ReaderEnterSafety
import Exec.Code.Body.Reader.Common.ReaderSafety
import Exec.Code.Body.Reader.Common.ReaderEnterWasm1
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxHeartbeats 2000000

private theorem if_reader_prefix (st : code.OpIterState) (data : Slice U8)
    (outer segment : List code.StackType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length) (capacity : st.ctrls.val.length < Usize.max) :
    code.read_if st data ⦃ out => ∀ bt, out.1 = .Ok bt → EntryPrefix st out.2 ⦄ := by
  unfold code.read_if
  step with code.read_block_type.raw_spec data st.pos as ⟨reply,_⟩
  cases reply with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨bt,next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with pop_with_type_prefix {st with pos := next} outer segment .I32 values base
      as ⟨status,middle,controls,position,rest,middleValues,restPrefix⟩
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      step with code.push_ctrl.spec middle .Then bt (by simpa [controls] using capacity)
        as ⟨after,afterControls,afterValues,afterPosition⟩
      intro actual accepted
      refine ⟨middle.ctrls.val, Control.frame middle .Then bt, afterControls, ?_, ?_⟩
      · simp [Control.frame, alloc.vec.Vec.len, afterValues]
      · simp only [Control.frame,alloc.vec.Vec.len]
        rw [afterValues]
        change middle.vals.val.take middle.vals.val.length <+: st.vals.val
        rw [List.take_length]
        rcases restPrefix with ⟨suffix,suffixEq⟩
        exact ⟨suffix,by rw [middleValues,values,← suffixEq,List.append_assoc]⟩

private theorem enter_reader_wasm1 {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) (kind : code.LabelKind)
    (read : Result (core.result.Result code.BlockType error.OpError × code.OpIterState))
    (normal : read ⦃ out => ∀ bt, out.1 = .Ok bt → EntryPrefix state out.2 ⦄)
    (observed : ObservedStack compiler state.vals.val)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max)
    (pcBound : compiler.function.code.val.length+1 < 2^32)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (ordinary : kind = .Block ∨ kind = .Loop ∨ kind = .Then) :
    CoreVisitor.run read (fun c s bt => runtime.compiler.control.FunctionCompiler.enter ops c s kind (Control.signature bt)) compiler ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  apply reader_run_reached _ _ compiler (fun s c => ObservedStack c s.vals.val)
  · exact WP.spec_mono normal (by simp)
  · intro out bt accepted
    rw [accepted,WP.spec_ok] at normal
    obtain ⟨prior,ctrl,controls,bound,height⟩ := (normal bt rfl).height_bound observed
    obtain ⟨signature,selected,_⟩ := wasm1_signature_select compiler.signatures (bt := bt)
    exact compiler_enter_total ops law compiler out ctrl prior kind (Control.signature bt) signature
      controls selected bound height coordinate pcBound codeFits sourceFits mapsFit framesFit ordinary

theorem compiler_block_reader_wasm1_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    {data env ctx bodyBt state} (p : Wasm1.Pending data env ctx bodyBt state)
    (observed : ObservedStack compiler state.vals.val)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max)
    (pcBound : compiler.function.code.val.length+1 < 2^32)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max) :
    CoreVisitor.run (code.read_block state data)
      (fun c s bt => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_block c s (Control.signature bt)) compiler ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  apply enter_reader_wasm1 ops law compiler state .Block _ _ observed coordinate pcBound codeFits sourceFits mapsFit framesFit (by simp)
  apply WP.spec_mono (code.read_block.raw_spec state data p.ctrl_capacity)
  rintro ⟨status,out⟩ effect bt accepted
  obtain ⟨decoded,values,controls⟩ := effect bt accepted
  dsimp only at values controls
  refine ⟨state.ctrls.val,Control.frame state .Block bt,controls,?_,?_⟩
  · simp [Control.frame,alloc.vec.Vec.len,values]
  · simp [Control.frame,alloc.vec.Vec.len,values]

theorem compiler_loop_reader_wasm1_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    {data env ctx bodyBt state} (p : Wasm1.Pending data env ctx bodyBt state)
    (observed : ObservedStack compiler state.vals.val)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max)
    (pcBound : compiler.function.code.val.length+1 < 2^32)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max) :
    CoreVisitor.run (code.read_loop state data)
      (fun c s bt => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_loop c s (Control.signature bt)) compiler ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  apply enter_reader_wasm1 ops law compiler state .Loop _ _ observed coordinate pcBound codeFits sourceFits mapsFit framesFit (by simp)
  apply WP.spec_mono (code.read_loop.raw_spec state data p.ctrl_capacity)
  rintro ⟨status,out⟩ effect bt accepted
  obtain ⟨decoded,values,controls⟩ := effect bt accepted
  dsimp only at values controls
  refine ⟨state.ctrls.val,Control.frame state .Loop bt,controls,?_,?_⟩
  · simp [Control.frame,alloc.vec.Vec.len,values]
  · simp [Control.frame,alloc.vec.Vec.len,values]

theorem compiler_if_reader_wasm1_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    {data env ctx bodyBt state} (p : Wasm1.Pending data env ctx bodyBt state)
    (observed : ObservedStack compiler state.vals.val)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max)
    (pcBound : compiler.function.code.val.length+1 < 2^32)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max) :
    CoreVisitor.run (code.read_if state data)
      (fun c s bt => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_if c s (Control.signature bt)) compiler ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  apply enter_reader_wasm1 ops law compiler state .Then _ _ observed coordinate pcBound codeFits sourceFits mapsFit framesFit (by simp)
  obtain ⟨C,outer,spine,header,base,typed,controls,values⟩ := p.opened
  exact if_reader_prefix state data outer p.current.vals values
    (by simp [Control.base,controls,base]) p.ctrl_capacity
end Exec.Code
