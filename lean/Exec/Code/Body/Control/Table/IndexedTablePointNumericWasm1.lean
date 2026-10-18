import Exec.Code.Body.Reader.Common.ReaderScalarScratchWasm1
import Exec.Code.Body.Reader.Common.ReaderScalarCodeMonotoneWasm1
import Exec.Code.Body.Reader.Table.IndexedTableReaderCompilerPreserved
import Exec.Code.Body.Control.Common.CumulativeEmbedding
import Exec.Code.Body.Reader.Table.ReaderScalarTablesWasm1
import Exec.Code.Body.Reader.Table.StructuredReaderCompilerNumericWithTables
import Exec.Code.Body.Reader.Float.StructuredReaderCompilerFloatWithTables
import Exec.Code.Body.Reader.Table.StructuredReaderCompilerSaturatingWithTables
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem IndexedTableReaderCompilerPointWasm1.numeric {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env ctx bodyBt st}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (includeCumulative : ∀ tables, CumulativeEmbedding tables.indirect C (emit tables))
    (point : IndexedTableReaderCompilerPointWasm1 emit initial before types functions returns locals data env ctx bodyBt st)
    (contextLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (op : Abs.Numeric.Instruction) 
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.pos.val]'inbounds = (UScalar.cast .U8 (integerOpcode op)))
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPointWasm1 emit initial after types functions returns locals data env ctx bodyBt out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have pairs := reader_numeric_tables_wasm1 p ops law before after out op byte accepted
  have depths := reader_numeric_depths_wasm1 p ops law before after out op byte accepted
  have growth := reader_numeric_code_mono_wasm1 p ops law before after out op byte accepted
  apply point.preserved_step pairs depths growth
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  letI : FloatEmbedding C (emit ((CompilerTables.ofFunction before.function).append future)) := ⟨fun h => (includeCumulative ((CompilerTables.ofFunction before.function).append future)).lift (.left h)⟩
  letI : CoreEmbedding C (emit ((CompilerTables.ofFunction before.function).append future)) := ⟨fun h => (includeCumulative ((CompilerTables.ofFunction before.function).append future)).lift (.left (.core h))⟩
  have embedding : LinearEmbedding locals (emit ((CompilerTables.ofFunction before.function).append future)) := by
    intro input instruction code output head
    exact (includeCumulative ((CompilerTables.ofFunction before.function).append future)).lift (.left (.core (.pure (by simpa only [contextLocals] using head))))
  obtain ⟨values,changed⟩ := state.numeric ops law embedding next advance inbounds out op sourceBound bodyBound byte accepted
  exact changed.point

theorem IndexedTableReaderCompilerPointWasm1.float_base {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env ctx bodyBt st}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (includeCumulative : ∀ tables, CumulativeEmbedding tables.indirect C (emit tables))
    (point : IndexedTableReaderCompilerPointWasm1 emit initial before types functions returns locals data env ctx bodyBt st)
    (contextLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (op : Abs.Float.Instruction) (baseOpcode : (floatOpcode op).val < 256)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.pos.val]'inbounds = (UScalar.cast .U8 (floatOpcode op)))
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx (UScalar.cast .U8 (floatOpcode op)) before = .ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPointWasm1 emit initial after types functions returns locals data env ctx bodyBt out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have pairs := reader_float_base_tables_wasm1 p ops law before after out op baseOpcode byte accepted
  have depths := reader_float_base_depths_wasm1 p ops law before after out op baseOpcode byte accepted
  have growth := reader_float_base_code_mono_wasm1 p ops law before after out op baseOpcode byte accepted
  apply point.preserved_step pairs depths growth
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  letI : FloatEmbedding C (emit ((CompilerTables.ofFunction before.function).append future)) := ⟨fun h => (includeCumulative ((CompilerTables.ofFunction before.function).append future)).lift (.left h)⟩
  letI : CoreEmbedding C (emit ((CompilerTables.ofFunction before.function).append future)) := ⟨fun h => (includeCumulative ((CompilerTables.ofFunction before.function).append future)).lift (.left (.core h))⟩
  obtain ⟨values,changed⟩ := state.float_base ops law C contextLocals next advance inbounds out op baseOpcode
    sourceBound bodyBound byte accepted
  exact changed.point


end Exec.Code
