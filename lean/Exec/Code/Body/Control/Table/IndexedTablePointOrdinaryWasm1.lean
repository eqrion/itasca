import Exec.Code.Body.Reader.Common.ReaderOrdinaryScratchWasm1
import Exec.Code.Body.Reader.Common.ReaderOrdinaryCodeMonotoneWasm1
import Exec.Code.Body.Reader.Table.StructuredReaderCompilerOrdinaryWithTables
import Exec.Code.Body.Reader.Table.IndexedTableReaderCompilerPreserved
import Exec.Code.Body.Control.Common.CumulativeEmbedding
import Exec.Code.Body.Reader.Table.ReaderOrdinaryTablesWasm1
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem IndexedTableReaderCompilerPointWasm1.ordinary {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types locals data env ctx bodyBt st}
    (contextLocals : C.LOCALS = locals)
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (includeCumulative : ∀ tables, CumulativeEmbedding tables.indirect C (emit tables))
    (point : IndexedTableReaderCompilerPointWasm1 emit initial before types (env.func_types.val.map EnvTranslation.funcType) (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt st)
    (metadata : FunctionParameterSlots initial env)
    (localsMatch : initial.function.locals = ctx.locals)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (bodyResults : Control.resultTypes bodyBt = ctx.results.val.map Translate.valueType)
    (opcode : U8) (ordinary : opcode ∈ readerOrdinaryOpcodes)
    (byte : data.val[st.pos.val]'inbounds = opcode)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx opcode before = .ok (.Ok (), out, after)) :
    IndexedTableReaderCompilerPointWasm1 emit initial after types (env.func_types.val.map EnvTranslation.funcType) (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have pairs := reader_ordinary_tables_wasm1 p ops law before after out opcode ordinary byte accepted
  have depths := reader_ordinary_depths_wasm1 p ops law before after out opcode ordinary byte accepted
  have growth := reader_ordinary_code_mono_wasm1 p ops law before after out opcode ordinary byte accepted
  apply point.preserved_step pairs depths growth
  intro future old
  have embedding : LinearEmbedding locals (emit ((CompilerTables.ofFunction before.function).append future)) := by
    intro input instruction code output h
    exact (includeCumulative ((CompilerTables.ofFunction before.function).append future)).lift (.left (.core (.pure (by simpa only [contextLocals] using h))))
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  exact state.ordinary ops law embedding metadata localsMatch next advance inbounds out sourceBound bodyBound bodyResults opcode ordinary byte accepted
end Exec.Code
