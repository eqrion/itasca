import Itasca.Runtime.Code.Body.Reader.Table.StructuredReaderCompilerState
import Itasca.Runtime.Code.Body.Reader.Table.StructuredReaderPrefixConst
import Itasca.Runtime.Code.Body.Reader.Table.StructuredReaderPrefixDeadBasic
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.const32 {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_I32_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_I32_CONST before = .ok (.Ok (), out, after)) :
    ∃ value, StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (Spec.i32Const value)) savedParents
      (savedCurrent.advance (.plain (Spec.i32Const value)) (Spec.i32Const value)
        savedCurrent.ctrl.polymorphic_base (savedCurrent.vals ++ [.Val .I32])) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    obtain ⟨value, post, compiled⟩ := structured_reader_prefix_const32_wasm2 p ops law initial before after out ctx rfl
      embedding state.compiled reach sourceBound bodyBound byte accepted
    exact ⟨value, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices, Spec.i32Const, ScalarConst.i64]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨value, post, compiled, dead⟩ := structured_reader_prefix_dead_const32_wasm2 p ops law initial before after out ctx rfl
      state.compiled reach byte accepted
    exact ⟨value, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices, Spec.i32Const, ScalarConst.i64]) compiled (by simp [dead])⟩

theorem StructuredReaderCompilerStateWasm2.const64 {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_I64_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_I64_CONST before = .ok (.Ok (), out, after)) :
    ∃ value, StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (ScalarConst.i64 value)) savedParents
      (savedCurrent.advance (.plain (ScalarConst.i64 value)) (ScalarConst.i64 value)
        savedCurrent.ctrl.polymorphic_base (savedCurrent.vals ++ [.Val .I64])) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    obtain ⟨value, post, compiled⟩ := structured_reader_prefix_const64_wasm2 p ops law initial before after out ctx rfl
      embedding state.compiled reach sourceBound bodyBound byte accepted
    exact ⟨value, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices, Spec.i32Const, ScalarConst.i64]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨value, post, compiled, dead⟩ := structured_reader_prefix_dead_const64_wasm2 p ops law initial before after out ctx rfl
      state.compiled reach byte accepted
    exact ⟨value, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices, Spec.i32Const, ScalarConst.i64]) compiled (by simp [dead])⟩

end Itasca.Runtime.Code
