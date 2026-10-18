import Exec.Code.Local.Lowering.Common.NumericEncoding
import Exec.Code.Body.Reader.Common.StructuredReaderPrefixSign
import Exec.Code.Body.Reader.Common.ReaderSignExtension
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerState
import Exec.Code.Body.Reader.Common.StructuredReaderPrefixNumeric
import Exec.Code.Body.Reader.Common.StructuredReaderPrefixDeadNumeric
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.numeric {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerStateWasm2 emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (op : Abs.Numeric.Instruction) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = (UScalar.cast .U8 (integerOpcode op)))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    ∃ values, StructuredReaderCompilerStateWasm2 emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance op.source) savedParents
      (savedCurrent.advance (.plain op.source) op.source
        savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    by_cases standard : (integerOpcode op).val < 192
    · obtain ⟨values, post, compiled⟩ := structured_reader_prefix_numeric_wasm2 p ops law initial before after out ctx rfl
        embedding state.compiled reach (state.reach.current reach) op standard sourceBound bodyBound byte accepted
      exact ⟨values, state.advance next advance inbounds post (integer_source_declared op _) compiled (fun _ => state.reach.current reach)⟩
    · obtain ⟨values, post, compiled⟩ := structured_reader_prefix_sign_wasm2 p ops law initial before after out ctx rfl
        embedding state.compiled reach (state.reach.current reach) op (by omega) sourceBound bodyBound byte accepted
      exact ⟨values, state.advance next advance inbounds post (integer_source_declared op _) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    by_cases standard : (integerOpcode op).val < 192
    · obtain ⟨values, post, compiled, dead⟩ := structured_reader_prefix_dead_numeric_wasm2 p ops law initial before after out ctx rfl
        state.compiled reach op standard byte accepted
      exact ⟨values, state.advance next advance inbounds post (integer_source_declared op _) compiled (by simp [dead])⟩
    · obtain ⟨values, post, compiled, dead⟩ := structured_reader_prefix_dead_sign_wasm2 p ops law initial before after out ctx rfl
        state.compiled reach op (by omega) byte accepted
      exact ⟨values, state.advance next advance inbounds post (integer_source_declared op _) compiled (by simp [dead])⟩

theorem StructuredReaderCompilerStateWasm1.numeric {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerStateWasm1 emit initial before types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (op : Abs.Numeric.Instruction) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.pos.val]'inbounds = (UScalar.cast .U8 (integerOpcode op)))
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    ∃ values, StructuredReaderCompilerStateWasm1 emit initial after types functions returns locals data env ctx bodyBt out
      parents (current.advance op.source) savedParents
      (savedCurrent.advance (.plain op.source) op.source
        savedCurrent.ctrl.polymorphic_base values) := by
  have baseOpcode : (integerOpcode op).val < 192 := by
    by_contra outside
    exact reader_integer_sign_wasm1_impossible ops before after {st with pos := next} out data env ctx op (by omega) accepted
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    obtain ⟨values, post, compiled⟩ := structured_reader_prefix_numeric_wasm1 p ops law initial before after out
      embedding state.compiled reach (state.reach.current reach) op baseOpcode sourceBound bodyBound byte accepted
    exact ⟨values, state.advance next advance inbounds post compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨values, post, compiled, dead⟩ := structured_reader_prefix_dead_numeric_wasm1 p ops law initial before after out
      state.compiled reach op baseOpcode byte accepted
    exact ⟨values, state.advance next advance inbounds post compiled (by simp [dead])⟩
end Exec.Code
