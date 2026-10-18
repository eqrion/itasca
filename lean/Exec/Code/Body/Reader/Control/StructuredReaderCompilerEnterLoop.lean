import Exec.Code.Body.Reader.Common.StructuredReaderCompilerState
import Exec.Code.Body.Reader.Control.ReaderControlBoundary
import Exec.Code.Body.Reader.Control.StructuredReaderPrefixLoopWasm1
import Exec.Code.Body.Reader.Control.StructuredReaderPrefixLoopDormantWasm1
import Exec.Code.Body.Reader.Control.StructuredReaderPrefixLoopWasm2
import Exec.Code.Body.Reader.Control.StructuredReaderPrefixLoopDormantWasm2
import Exec.Code.Body.Reader.Common.ReaderKnownFrontEntry
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm1.enter_loop {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm1 emit initial before types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState)
    (byte : data.val[st.pos.val]'inbounds = code.OP_LOOP)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx code.OP_LOOP before = .ok (.Ok (), out, after)) :
    ∃ bt front, StructuredReaderCompilerStateWasm1 emit initial after types functions returns locals data env ctx bodyBt out
      (parents ++ [current]) (SourceScope.enterLoop (Control.blockType bt) front [] (Control.resultTypes bt) before.function.code.val.length before.reachable)
      (savedParents ++ [{savedCurrent with vals := savedCurrent.vals}]) (Wasm1.Frames.Saved.fresh out .loop bt) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    obtain ⟨bt, front, post, compiled, same, reachable, fronts⟩ :=
      structured_reader_prefix_loop_wasm1 p ops law initial before after out
        types functions returns locals parents current state.compiled state.sources state.reach state.fronts reach byte accepted
    refine ⟨bt, front, compiled, ?_, ?_, reachable, fronts, ?_⟩
    · exact post.boundary rfl
    · exact same
    · apply post.known_fronts state.knownFronts _
      · intro entered
        apply state.reach.current
        simpa only [SourceScope.enterLoop, reach] using entered
      · intro entered
        apply state.compiled.known
        simpa only [SourceScope.enterLoop, reach] using entered
  | false =>
    obtain ⟨bt, front, post, compiled, same, reachable, fronts⟩ :=
      structured_reader_prefix_loop_dead_wasm1 p ops law initial before after out
        types functions returns locals parents current state.compiled state.sources state.reach state.fronts reach byte accepted
    refine ⟨bt, front, compiled, ?_, ?_, reachable, fronts, ?_⟩
    · exact post.boundary rfl
    · exact same
    · apply post.known_fronts state.knownFronts _
      · intro entered
        apply state.reach.current
        simpa only [SourceScope.enterLoop, reach] using entered
      · intro entered
        apply state.compiled.known
        simpa only [SourceScope.enterLoop, reach] using entered

theorem StructuredReaderCompilerStateWasm2.enter_loop {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_LOOP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_LOOP before = .ok (.Ok (), out, after)) :
    ∃ bt ins outs remaining base front, StructuredReaderCompilerStateWasm2 emit initial after types functions returns locals data env ctx.locals index ft out
      (parents ++ [current]) (SourceScope.enterLoop (Wasm2.blockType bt) front (ins.map Translate.valueType) (outs.map Translate.valueType) before.function.code.val.length before.reachable)
      (savedParents ++ [{savedCurrent with vals := remaining}]) (Wasm2.Frames.Saved.fresh base .loop bt ins outs) := by
  let p := state.boundary.pending next advance inbounds
  have signaturesBefore : SignatureSequence before.signatures.val env.types.val := by
    simpa only [state.compiled.metadata.fields.1] using signatures
  cases reach : before.reachable with
  | true =>
    obtain ⟨bt, ins, outs, remaining, base, front, post, compiled, same, reachable, fronts⟩ :=
      structured_reader_prefix_loop_wasm2 p ops law initial before after out ctx
        types functions returns locals parents current state.compiled state.sources state.reach state.fronts reach signaturesBefore byte accepted
    refine ⟨bt, ins, outs, remaining, base, front, compiled, ?_, ?_, reachable, fronts, ?_⟩
    · exact post.boundary (.inr (.inl rfl))
    · exact same
    · apply post.known_fronts state.knownFronts _
      · intro entered
        apply state.reach.current
        simpa only [SourceScope.enterLoop, reach] using entered
      · intro entered
        apply state.compiled.known
        simpa only [SourceScope.enterLoop, reach] using entered
  | false =>
    obtain ⟨bt, ins, outs, remaining, base, front, post, compiled, same, reachable, fronts⟩ :=
      structured_reader_prefix_loop_dead_wasm2 p ops law initial before after out ctx
        types functions returns locals parents current state.compiled state.sources state.reach state.fronts reach signaturesBefore byte accepted
    refine ⟨bt, ins, outs, remaining, base, front, compiled, ?_, ?_, reachable, fronts, ?_⟩
    · exact post.boundary (.inr (.inl rfl))
    · exact same
    · apply post.known_fronts state.knownFronts _
      · intro entered
        apply state.reach.current
        simpa only [SourceScope.enterLoop, reach] using entered
      · intro entered
        apply state.compiled.known
        simpa only [SourceScope.enterLoop, reach] using entered

end Exec.Code
