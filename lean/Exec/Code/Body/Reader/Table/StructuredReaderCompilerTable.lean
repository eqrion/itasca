import Exec.Code.Body.Reader.Table.StructuredReaderCompilerStateWithTables
import Exec.Code.Body.Reader.Table.StructuredReaderPrefixTableWasm1
import Exec.Code.Body.Reader.Table.StructuredReaderPrefixTableWasm2
import Itasca.Wasm2.Trace.TableBytes
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWithTablesWasm1.br_table {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {jumpTables emit types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWithTablesWasm1 jumpTables emit initial before types functions returns locals
      data env ctx bodyBt st parents current savedParents savedCurrent)
    (boundary : CompilerTableBoundary before)
    (next : Usize) (advance : next.val=st.pos.val+1) (inbounds : st.pos.val<data.length)
    (out : code.OpIterState) (depths : List U32) (fallback : U32) (endPos : Usize)
    (encoded : BrTable.Decoded data next depths fallback endPos)
    (futureTables : List U32) (tableEq : jumpTables=after.function.jump_tables.val++futureTables)
    (gate : ∀ stack selector start len, emit (stack++[.I32]) (BrTable.instruction depths fallback)
      [.JumpTable selector start len] stack)
    (byte : data.val[st.pos.val]'inbounds=code.OP_BR_TABLE)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos:=next} data env ctx code.OP_BR_TABLE before=.ok (.Ok (),out,after)) :
    StructuredReaderCompilerStateWithTablesWasm1 jumpTables emit initial after types functions returns locals
      data env ctx bodyBt out parents (current.advance (BrTable.instruction depths fallback)) savedParents
      (savedCurrent.advance (.plain (BrTable.instruction depths fallback)) (BrTable.instruction depths fallback) true []) ∧
    CompilerTableBoundary after := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨post,compiled,afterBoundary,dead⟩ := structured_reader_prefix_table_wasm1 p ops law initial before after out
    state.compiled state.sources state.fronts state.reach.current boundary depths fallback endPos encoded
    futureTables tableEq gate byte accepted
  exact ⟨state.advance next advance inbounds post compiled (by simp [dead]),afterBoundary⟩

theorem StructuredReaderCompilerStateWithTablesWasm2.br_table {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {jumpTables emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWithTablesWasm2 jumpTables emit initial before types functions returns locals
      data env ctx.locals index ft st parents current savedParents savedCurrent)
    (boundary : CompilerTableBoundary before)
    (next : Usize) (advance : next.val=st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (out : code.BodyState) (depths : List U32) (fallback : U32) (endPos : Usize)
    (encoded : BrTable.Decoded data next depths fallback endPos)
    (futureTables : List U32) (tableEq : jumpTables=after.function.jump_tables.val++futureTables)
    (gate : ∀ stack selector start len, emit (stack++[.I32]) (BrTable.instruction depths fallback)
      [.JumpTable selector start len] stack)
    (byte : data.val[st.core.pos.val]'inbounds=0x0e#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core:={st.core with pos:=next}} data env ctx index .Wasm2 0x0e#u8 before=.ok (.Ok (),out,after)) :
    StructuredReaderCompilerStateWithTablesWasm2 jumpTables emit initial after types functions returns locals
      data env ctx.locals index ft out parents (current.advance (BrTable.instruction depths fallback)) savedParents
      (savedCurrent.advance (.plain (BrTable.instruction depths fallback)) (BrTable.instruction depths fallback) true []) ∧
    CompilerTableBoundary after := by
  rw [Wasm2.CallbackTrace.dispatch_br_table] at accepted
  let p := state.boundary.pending next advance inbounds
  obtain ⟨post,compiled,afterBoundary,dead⟩ := structured_reader_prefix_table_wasm2 p ops law initial before after out
    state.compiled state.sources state.fronts state.reach.current boundary depths fallback endPos encoded
    futureTables tableEq gate byte accepted
  refine ⟨state.advance next advance inbounds post ?_ compiled (by simp [dead]),afterBoundary⟩
  simp [DeclaredReferences.Instruction,DeclaredReferences.instructionIndices,BrTable.instruction]
end Exec.Code
