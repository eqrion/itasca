import Exec.Code.Body.Reader.Common.StructuredReaderCompilerState
import Exec.Code.Body.Reader.Control.ReaderControlBoundary
import Exec.Code.Body.Reader.Control.StructuredReaderPrefixIfWasm1
import Exec.Code.Body.Reader.Control.StructuredReaderPrefixIfDormantWasm1
import Exec.Code.Body.Reader.Control.StructuredReaderPrefixIfWasm2
import Exec.Code.Body.Reader.Control.StructuredReaderPrefixIfDormantWasm2
import Exec.Code.Body.Reader.Common.ReaderKnownFrontEntry
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm1.enter_if {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm1 emit initial before types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState)
    (byte : data.val[st.pos.val]'inbounds = code.OP_IF)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx code.OP_IF before = .ok (.Ok (), out, after)) :
    ∃ bt remaining front condition, StructuredReaderCompilerStateWasm1 emit initial after types functions returns locals data env ctx bodyBt out
      (parents ++ [current]) (SourceScope.enterIf (Control.blockType bt) condition front [] (Control.resultTypes bt) before.function.code.val.length before.reachable)
      (savedParents ++ [{savedCurrent with vals := remaining}]) (Wasm1.Frames.Saved.fresh out .then_ bt) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    obtain ⟨bt, remaining, front, condition, post, compiled, same, reachable, fronts⟩ :=
      structured_reader_prefix_if_wasm1 p ops law initial before after out
        types functions returns locals parents current state.compiled state.sources state.reach state.fronts reach byte accepted
    refine ⟨bt, remaining, front, condition, compiled, ?_, ?_, reachable, fronts, ?_⟩
    · exact post.boundary rfl
    · exact same
    · apply post.known_fronts state.knownFronts _
      · intro entered
        apply state.reach.current
        simpa only [SourceScope.enterIf, reach] using entered
      · intro entered
        apply state.compiled.known
        simpa only [SourceScope.enterIf, reach] using entered
  | false =>
    obtain ⟨bt, remaining, front, post, compiled, same, reachable, fronts⟩ :=
      structured_reader_prefix_if_dead_wasm1 p ops law initial before after out
        types functions returns locals parents current state.compiled state.sources state.reach state.fronts reach byte accepted
    refine ⟨bt, remaining, front, 0#u32, compiled, ?_, ?_, reachable, fronts, ?_⟩
    · exact post.boundary rfl
    · exact same
    · apply post.known_fronts state.knownFronts _
      · intro entered
        apply state.reach.current
        simpa only [SourceScope.enterIf, reach] using entered
      · intro entered
        apply state.compiled.known
        simpa only [SourceScope.enterIf, reach] using entered

theorem StructuredReaderCompilerStateWasm2.enter_if {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_IF)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_IF before = .ok (.Ok (), out, after)) :
    ∃ bt ins outs remaining base front condition, StructuredReaderCompilerStateWasm2 emit initial after types functions returns locals data env ctx.locals index ft out
      (parents ++ [current]) (SourceScope.enterIf (Wasm2.blockType bt) condition front (ins.map Translate.valueType) (outs.map Translate.valueType) before.function.code.val.length before.reachable)
      (savedParents ++ [{savedCurrent with vals := remaining}]) (Wasm2.Frames.Saved.fresh base .then_ bt ins outs) := by
  let p := state.boundary.pending next advance inbounds
  have signaturesBefore : SignatureSequence before.signatures.val env.types.val := by
    simpa only [state.compiled.metadata.fields.1] using signatures
  cases reach : before.reachable with
  | true =>
    obtain ⟨bt, ins, outs, remaining, base, front, condition, post, compiled, same, reachable, fronts⟩ :=
      structured_reader_prefix_if_wasm2 p ops law initial before after out ctx
        types functions returns locals parents current state.compiled state.sources state.reach state.fronts reach signaturesBefore byte accepted
    refine ⟨bt, ins, outs, remaining, base, front, condition, compiled, ?_, ?_, reachable, fronts, ?_⟩
    · exact post.boundary (.inr (.inr rfl))
    · exact same
    · apply post.known_fronts state.knownFronts _
      · intro entered
        apply state.reach.current
        simpa only [SourceScope.enterIf, reach] using entered
      · intro entered
        apply state.compiled.known
        simpa only [SourceScope.enterIf, reach] using entered
  | false =>
    obtain ⟨bt, ins, outs, remaining, base, front, post, compiled, same, reachable, fronts⟩ :=
      structured_reader_prefix_if_dead_wasm2 p ops law initial before after out ctx
        types functions returns locals parents current state.compiled state.sources state.reach state.fronts reach signaturesBefore byte accepted
    refine ⟨bt, ins, outs, remaining, base, front, 0#u32, compiled, ?_, ?_, reachable, fronts, ?_⟩
    · exact post.boundary (.inr (.inr rfl))
    · exact same
    · apply post.known_fronts state.knownFronts _
      · intro entered
        apply state.reach.current
        simpa only [SourceScope.enterIf, reach] using entered
      · intro entered
        apply state.compiled.known
        simpa only [SourceScope.enterIf, reach] using entered

end Exec.Code
