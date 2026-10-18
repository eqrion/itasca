import Exec.Code.Body.Reader.Table.TableReaderCompilerPreserved
import Exec.Code.Body.Control.Common.CumulativeEmbedding
import Exec.Code.Body.Reader.Table.ReaderExtraTables
import Exec.Code.Body.Lowering.Float.FloatEmbedding
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem TableReaderCompilerPointWasm2.core_extra {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st}
    (C : context)
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (includeCumulative : ∀ tables, CumulativeEmbedding tables.indirect C (emit tables))
    (point : TableReaderCompilerPointWasm2 emit initial before types functions returns locals data env ctx.locals index ft st)
    (contextLocals : C.LOCALS = locals)
    (contextGlobals : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (opcode : U8) (covered : opcode.val ∈ [27,35,36,67,68,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62])
    (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    TableReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have pairs := reader_core_extra_tables_wasm2 p ops law before after out ctx rfl opcode covered byte accepted
  apply point.preserved_step pairs
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  letI : FloatEmbedding C (emit ((CompilerTables.ofFunction before.function).append future)) := ⟨fun h => (includeCumulative ((CompilerTables.ofFunction before.function).append future)).lift (.left h)⟩
  letI : CoreEmbedding C (emit ((CompilerTables.ofFunction before.function).append future)) := ⟨fun h => (includeCumulative ((CompilerTables.ofFunction before.function).append future)).lift (.left (.core h))⟩
  exact state.core_extra ops law C contextLocals contextGlobals contextMemories next advance inbounds out sourceBound bodyBound opcode covered byte accepted
end Exec.Code
