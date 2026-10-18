import Exec.Code.Body.Reader.Control.ReaderControlScratchWasm1
import Exec.Code.Body.Reader.Control.ReaderControlCodeMonotoneWasm1
import Exec.Code.Body.Control.Control.CumulativePointControl
import Exec.Code.Body.Reader.Table.IndexedTableReaderCompilerPreserved
import Exec.Code.Body.Control.Common.CumulativeEmbedding
import Exec.Code.Body.Reader.Table.ReaderControlTablesWasm1
import Exec.Code.Body.Reader.Table.StructuredReaderCompilerScopesWithTables
import Exec.Code.Body.Reader.Table.StructuredReaderCompilerElseWithTables
import Exec.Code.Body.Reader.Table.StructuredReaderCompilerEndWasm1WithTables
import Exec.Code.Body.Reader.Table.StructuredReaderCompilerRootWithTables
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem IndexedTableReaderCompilerPointWasm1.scope_step {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx bodyBt st}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (point : IndexedTableReaderCompilerPointWasm1 emit initial before types functions returns locals data env ctx bodyBt st)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (opcode : U8) (supported : ScopeOpcode opcode)
    (byte : data.val[st.pos.val]'inbounds = opcode)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx opcode before = .ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPointWasm1 emit initial after types functions returns locals data env ctx bodyBt out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have pairs := reader_scope_tables_wasm1 p ops law before after out opcode supported byte accepted
  have depths := reader_scope_depths_wasm1 p ops law before after out opcode supported byte accepted
  have growth := reader_scope_code_mono_wasm1 p ops law before after out opcode supported byte accepted
  apply point.preserved_step pairs depths growth
  intro future old
  exact old.scope_step ops law next advance inbounds out sourceBound opcode supported byte accepted

theorem IndexedTableReaderCompilerPointWasm1.else_ {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx bodyBt st}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (point : IndexedTableReaderCompilerPointWasm1 emit initial before types functions returns locals data env ctx bodyBt st)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (initialLocals : LocalLayout initial)
    (byte : data.val[st.pos.val]'inbounds = 5#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx 5#u8 before = .ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPointWasm1 emit initial after types functions returns locals data env ctx bodyBt out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have pairs := reader_else_tables_wasm1 p ops law before after out byte accepted
  have depths := reader_else_depths_wasm1 p ops law before after out byte accepted
  have growth := reader_else_code_mono_wasm1 p ops law before after out byte accepted
  apply point.preserved_step pairs depths growth
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  exact state.else_ ops law initialLocals next advance inbounds out (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)

end Exec.Code
