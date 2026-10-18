import Exec.Code.Body.Reader.Common.StructuredReaderCompilerState
import Exec.Code.Body.Reader.Common.StructuredReaderPrefixUnreachable
import Exec.Code.Body.Reader.Control.StructuredReaderPrefixReturn
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.unreachable {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_UNREACHABLE)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_UNREACHABLE before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerStateWasm2 emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.UNREACHABLE)) savedParents
      (savedCurrent.advance (.plain (.UNREACHABLE)) (.UNREACHABLE)
        true []) := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨post, compiled, dead⟩ := structured_reader_prefix_unreachable_wasm2 p ops law initial before after out ctx rfl
    state.compiled byte accepted
  exact state.advance next advance inbounds post
    (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])

theorem StructuredReaderCompilerStateWasm1.unreachable {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm1 emit initial before types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState)
    (byte : data.val[st.pos.val]'inbounds = code.OP_UNREACHABLE)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx code.OP_UNREACHABLE before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerStateWasm1 emit initial after types functions returns locals data env ctx bodyBt out
      parents (current.advance (.UNREACHABLE)) savedParents
      (savedCurrent.advance (.plain (.UNREACHABLE)) (.UNREACHABLE)
        true []) := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨post, compiled, dead⟩ := structured_reader_prefix_unreachable_wasm1 p ops law initial before after out
    state.compiled byte accepted
  exact state.advance next advance inbounds post compiled (by simp [dead])
theorem StructuredReaderCompilerStateWasm2.return_ {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 emit initial before types functions (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_RETURN)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_RETURN before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerStateWasm2 emit initial after types functions (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft out
      parents (current.advance (.RETURN)) savedParents
      (savedCurrent.advance (.plain (.RETURN)) (.RETURN)
        true []) := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨post, compiled, dead⟩ := structured_reader_prefix_return_wasm2 p ops law initial before after out ctx
    state.compiled state.sources state.reach.current sourceBound bodyBound
      (by simpa only [p, ReaderBoundaryWasm2.pending, global_simps] using byte) (by simpa only [global_simps] using accepted)
  exact state.advance next advance inbounds post
    (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])

theorem StructuredReaderCompilerStateWasm1.return_ {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm1 emit initial before types functions (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (bodyResults : Control.resultTypes bodyBt = ctx.results.val.map Translate.valueType)
    (byte : data.val[st.pos.val]'inbounds = code.OP_RETURN)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx code.OP_RETURN before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerStateWasm1 emit initial after types functions (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt out
      parents (current.advance (.RETURN)) savedParents
      (savedCurrent.advance (.plain (.RETURN)) (.RETURN)
        true []) := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨post, compiled, dead⟩ := structured_reader_prefix_return_wasm1 p ops law initial before after out
    state.compiled state.sources bodyResults state.reach.current sourceBound bodyBound byte accepted
  exact state.advance next advance inbounds post compiled (by simp [dead])
end Exec.Code
