import Exec.Code.Body.Reader.Common.ReaderExtraScratchWasm1
import Exec.Code.Body.Reader.Common.ReaderExtraCodeMonotoneWasm1
import Exec.Code.Body.Reader.Table.StructuredReaderCompilerExtraWithTables
import Exec.Code.Body.Reader.Table.IndexedTableReaderCompilerPreserved
import Exec.Code.Body.Control.Common.CumulativeEmbedding
import Exec.Code.Body.Reader.Table.ReaderExtraTablesWasm1
import Exec.Code.Body.Lowering.Float.FloatEmbedding
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem IndexedTableReaderCompilerPointWasm1.core_extra {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx bodyBt st}
    (C : context)
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (includeCumulative : ∀ tables, CumulativeEmbedding tables.indirect C (emit tables))
    (point : IndexedTableReaderCompilerPointWasm1 emit initial before types functions returns locals data env ctx bodyBt st)
    (contextLocals : C.LOCALS = locals)
    (contextGlobals : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (opcode : U8) (covered : opcode.val ∈ [27,35,36,67,68,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62])
    (byte : data.val[st.pos.val]'inbounds = opcode)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx opcode before = .ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPointWasm1 emit initial after types functions returns locals data env ctx bodyBt out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have pairs := reader_core_extra_tables_wasm1 p ops law before after out opcode covered byte accepted
  have depths := reader_core_extra_depths_wasm1 p ops law before after out opcode covered byte accepted
  have growth := reader_core_extra_code_mono_wasm1 p ops law before after out opcode covered byte accepted
  apply point.preserved_step pairs depths growth
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  letI : FloatEmbedding C (emit ((CompilerTables.ofFunction before.function).append future)) := ⟨fun h => (includeCumulative ((CompilerTables.ofFunction before.function).append future)).lift (.left h)⟩
  letI : CoreEmbedding C (emit ((CompilerTables.ofFunction before.function).append future)) := ⟨fun h => (includeCumulative ((CompilerTables.ofFunction before.function).append future)).lift (.left (.core h))⟩
  exact state.core_extra ops law C contextLocals contextGlobals contextMemories next advance inbounds out sourceBound bodyBound opcode covered byte accepted
end Exec.Code
