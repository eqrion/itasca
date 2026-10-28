import Itasca.Runtime.Code.Body.Reader.Table.IndexedTableReaderCompilerPoint
import Itasca.Runtime.Code.Body.Reader.Table.StructuredReaderCompilerTable
import Itasca.Runtime.Code.Body.Reader.Table.ReaderTableDecoded
import Itasca.Runtime.Code.Body.Relations.Table.BranchTableTables
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem IndexedTableReaderCompilerPointWasm2.br_table {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial before types functions returns locals
      data env ctx.locals index ft st)
    (next : Usize) (advance : next.val=st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (out : code.BodyState)
    (gate : ∀ tables depths fallback stack selector start len,
      emit tables (stack++[.I32]) (BrTable.instruction depths fallback) [.JumpTable selector start len] stack)
    (byte : data.val[st.core.pos.val]'inbounds=0x0e#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core:={st.core with pos:=next}} data env ctx index .Wasm2 0x0e#u8 before=.ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have read := accepted
  rw [Wasm2.CallbackTrace.dispatch_br_table] at read
  obtain ⟨depths,fallback,decoded⟩ := reader_table_decoded_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) p before after out read
  obtain ⟨targets,tablesEq⟩ := compiler_reader_table_tables_wasm2 ops law before after _ out data env
    p.opened.shape.core depths fallback out.core.pos decoded read
  obtain ⟨_,_,_,boundary,_,_⟩ := compiler_reader_table_effect_wasm2 ops law before after _ out
    data env p.opened.shape.core depths fallback out.core.pos decoded point.tables read
  apply point.append_step ⟨[],[],[],targets⟩ tablesEq boundary
  intro future held
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := held
  obtain ⟨advanced,_⟩ := state.br_table ops law point.tables next advance inbounds out depths fallback out.core.pos decoded
    future.jumpTables rfl (gate _ depths fallback) byte accepted
  exact advanced.point
end Itasca.Runtime.Code
