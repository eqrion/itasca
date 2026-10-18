import Exec.Code.Body.Reader.Common.ReaderCompilerState
import Exec.Code.Body.Reader.Calls.ReaderPrefixCall
import Exec.Code.Body.Reader.Calls.ReaderPrefixDeadCall
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem ReaderCompilerStateWasm2.call {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : ReaderCompilerStateWasm2 initial before types (env.func_types.val.map EnvTranslation.funcType) returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (metadata : FunctionParameterSlots initial env)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_CALL)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_CALL before = .ok (.Ok (), out, after)) :
    ∃ (callee : U32) (values : List code.StackType), ReaderCompilerStateWasm2 initial after types (env.func_types.val.map EnvTranslation.funcType) returns locals data env ctx.locals index ft out
      parents (current.advance (.CALL (.mk_uN callee.val))) savedParents
      (savedCurrent.advance (.plain (.CALL (.mk_uN callee.val))) (.CALL (.mk_uN callee.val))
        savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    obtain ⟨callee, ft, values, found, post, compiled⟩ := reader_prefix_call_wasm2 p ops law initial before after out ctx
      state.compiled reach (state.reach.current reach) metadata sourceBound bodyBound byte accepted
    exact ⟨callee, values, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨callee, values, post, compiled, dead⟩ := reader_prefix_dead_call_wasm2 p ops law initial before after out ctx
      state.compiled reach byte accepted
    exact ⟨callee, values, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])⟩

theorem ReaderCompilerStateWasm1.call {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : ReaderCompilerStateWasm1 initial before types (env.func_types.val.map EnvTranslation.funcType) returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (metadata : FunctionParameterSlots initial env)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.pos.val]'inbounds = code.OP_CALL)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx code.OP_CALL before = .ok (.Ok (), out, after)) :
    ∃ (callee : U32) (values : List code.StackType), ReaderCompilerStateWasm1 initial after types (env.func_types.val.map EnvTranslation.funcType) returns locals data env ctx bodyBt out
      parents (current.advance (.CALL (.mk_uN callee.val))) savedParents
      (savedCurrent.advance (.plain (.CALL (.mk_uN callee.val))) (.CALL (.mk_uN callee.val))
        savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    obtain ⟨callee, ft, values, found, post, compiled⟩ := reader_prefix_call_wasm1 p ops law initial before after out
      state.compiled reach (state.reach.current reach) metadata sourceBound bodyBound byte accepted
    exact ⟨callee, values, state.advance next advance inbounds post compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨callee, values, post, compiled, dead⟩ := reader_prefix_dead_call_wasm1 p ops law initial before after out
      state.compiled reach byte accepted
    exact ⟨callee, values, state.advance next advance inbounds post compiled (by simp [dead])⟩
end Exec.Code
