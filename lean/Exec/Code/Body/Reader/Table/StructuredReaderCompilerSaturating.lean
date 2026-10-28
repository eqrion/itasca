import Exec.Code.Body.Control.Common.StructuredScalarEmbedding
import Exec.Code.Local.Lowering.Float.FloatEncoding
import Exec.Code.Body.Reader.Table.StructuredReaderCompilerState
import Exec.Code.Body.Reader.Table.StructuredReaderPrefixSaturating
import Exec.Code.Body.Reader.Table.StructuredReaderPrefixDeadSaturating
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.float_saturating {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) (contextCodeLocals : C.LOCALS = locals) {emit} [ScalarEmbedding C emit]
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (op : Abs.Float.Instruction) (extension : 256 ≤ (floatOpcode op).val)
    (subopcode : U32) (endPosition : Usize)
    (subopcodeEq : subopcode.val = (floatOpcode op).val - 256)
    (decoded : Leb128.Decoded data next subopcode endPosition)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 252#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 252#u8 before = .ok (.Ok (), out, after)) :
    ∃ values, StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance op.source) savedParents
      (savedCurrent.advance (.plain op.source) op.source
        savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    obtain ⟨values, post, compiled⟩ := structured_reader_prefix_saturating_wasm2 p ops law initial before after out ctx rfl
      C contextCodeLocals state.compiled reach (state.reach.current reach) op extension subopcode endPosition subopcodeEq decoded sourceBound bodyBound byte accepted
    exact ⟨values, state.advance next advance inbounds post (float_source_declared op _) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨values, post, compiled, dead⟩ := structured_reader_prefix_dead_saturating_wasm2 p ops law initial before after out ctx rfl
      state.compiled reach op extension subopcode endPosition subopcodeEq decoded byte accepted
    exact ⟨values, state.advance next advance inbounds post (float_source_declared op _) compiled (by simp [dead])⟩

end Itasca.Runtime.Code
