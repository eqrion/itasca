import Exec.Code.Body.Reader.Simd.ReaderSimdEventPrefix
import Exec.Code.Body.Reader.Simd.ReaderSimdEventDispatch
import Exec.Code.Body.Reader.Table.StructuredReaderCompilerPoint
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Actual SIMD dispatch extends the same canonical source zipper and the
structured compiler state, including dead code and exact table growth. -/
theorem StructuredReaderCompilerStateWasm2.simd {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) (contextLocals : C.LOCALS = locals)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    {emit} [SimdEmbedding after.function.simd.val after.function.v128_pool.val C emit]
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 0xfd#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 0xfd#u8 before = .ok (.Ok (),out,after)) :
    ∃ extra, CompilerTables.ofFunction after.function = (CompilerTables.ofFunction before.function).append extra ∧
      StructuredReaderCompilerPointWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨event⟩ := reader_simd_event_wasm2 p ops before after out ctx C contextMemories byte accepted
  obtain ⟨extra,tables,compiled,mono⟩ := event.prefix law contextLocals state.compiled
    state.reach.current sourceBound bodyBound
  exact ⟨extra,tables,(state.advance next advance inbounds event.post (event.meaning.declared _) compiled mono).point⟩
end Exec.Code
