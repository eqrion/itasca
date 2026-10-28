import Exec.Code.Body.Reader.Table.StructuredReaderCompilerState
import Exec.Code.Body.Reader.Table.StructuredReaderPrefixUnreachable
import Exec.Code.Body.Reader.Table.StructuredReaderPrefixReturn
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.unreachable {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_UNREACHABLE)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_UNREACHABLE before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.UNREACHABLE)) savedParents
      (savedCurrent.advance (.plain (.UNREACHABLE)) (.UNREACHABLE)
        true []) := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨post, compiled, dead⟩ := structured_reader_prefix_unreachable_wasm2 p ops law initial before after out ctx rfl
    state.compiled byte accepted
  exact state.advance next advance inbounds post
    (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])

theorem StructuredReaderCompilerStateWasm2.return_ {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_RETURN)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_RETURN before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft out
      parents (current.advance (.RETURN)) savedParents
      (savedCurrent.advance (.plain (.RETURN)) (.RETURN)
        true []) := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨post, compiled, dead⟩ := structured_reader_prefix_return_wasm2 p ops law initial before after out ctx
    state.compiled state.sources state.reach.current sourceBound bodyBound
      (by simpa only [p, ReaderBoundaryWasm2.pending, global_simps] using byte) (by simpa only [global_simps] using accepted)
  exact state.advance next advance inbounds post
    (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])

end Itasca.Runtime.Code
