import Exec.Code.Body.Reader.Table.StructuredReaderCompilerTable
import Exec.Code.Body.Reader.Table.ReaderTableDecoded
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWithTablesWasm1.br_table_accepted {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {jumpTables emit types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWithTablesWasm1 jumpTables emit initial before types functions returns locals
      data env ctx bodyBt st parents current savedParents savedCurrent)
    (boundary : CompilerTableBoundary before)
    (next : Usize) (advance : next.val=st.pos.val+1) (inbounds : st.pos.val<data.length)
    (out : code.OpIterState)
    (futureTables : List U32) (tableEq : jumpTables=after.function.jump_tables.val++futureTables)
    (gate : ∀ depths fallback stack selector start len, emit (stack++[.I32]) (BrTable.instruction depths fallback)
      [.JumpTable selector start len] stack)
    (byte : data.val[st.pos.val]'inbounds=code.OP_BR_TABLE)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos:=next} data env ctx code.OP_BR_TABLE before=.ok (.Ok (),out,after)) :
    ∃ depths fallback, BrTable.Decoded data next depths fallback out.pos ∧
    StructuredReaderCompilerStateWithTablesWasm1 jumpTables emit initial after types functions returns locals
      data env ctx bodyBt out parents (current.advance (BrTable.instruction depths fallback)) savedParents
      (savedCurrent.advance (.plain (BrTable.instruction depths fallback)) (BrTable.instruction depths fallback) true []) ∧
    CompilerTableBoundary after := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨fallback,common,collected,read,_⟩ := reader_table_dispatch_wasm1
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) {st with pos:=next} out data env ctx before after accepted
  obtain ⟨depths,decoded⟩ := reader_table_decoded_wasm1
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) p before collected out fallback common read
  exact ⟨depths,fallback,decoded,state.br_table ops law boundary next advance inbounds out depths fallback out.pos
    decoded futureTables tableEq (gate depths fallback) byte accepted⟩

theorem StructuredReaderCompilerStateWithTablesWasm2.br_table_accepted {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {jumpTables emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWithTablesWasm2 jumpTables emit initial before types functions returns locals
      data env ctx.locals index ft st parents current savedParents savedCurrent)
    (boundary : CompilerTableBoundary before)
    (next : Usize) (advance : next.val=st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (out : code.BodyState)
    (futureTables : List U32) (tableEq : jumpTables=after.function.jump_tables.val++futureTables)
    (gate : ∀ depths fallback stack selector start len, emit (stack++[.I32]) (BrTable.instruction depths fallback)
      [.JumpTable selector start len] stack)
    (byte : data.val[st.core.pos.val]'inbounds=0x0e#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core:={st.core with pos:=next}} data env ctx index .Wasm2 0x0e#u8 before=.ok (.Ok (),out,after)) :
    ∃ depths fallback, BrTable.Decoded data next depths fallback out.core.pos ∧
    StructuredReaderCompilerStateWithTablesWasm2 jumpTables emit initial after types functions returns locals
      data env ctx.locals index ft out parents (current.advance (BrTable.instruction depths fallback)) savedParents
      (savedCurrent.advance (.plain (BrTable.instruction depths fallback)) (BrTable.instruction depths fallback) true []) ∧
    CompilerTableBoundary after := by
  let p := state.boundary.pending next advance inbounds
  have read := accepted
  rw [Wasm2.CallbackTrace.dispatch_br_table] at read
  obtain ⟨depths,fallback,decoded⟩ := reader_table_decoded_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) p before after out read
  exact ⟨depths,fallback,decoded,state.br_table ops law boundary next advance inbounds out depths fallback out.core.pos
    decoded futureTables tableEq (gate depths fallback) byte accepted⟩
end Exec.Code
