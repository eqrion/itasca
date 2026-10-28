import Exec.Code.Body.Reader.Table.StructuredReaderCompilerState
import Exec.Code.Body.Reader.Table.StructuredReaderPrefixTableWasm2
import Itasca.Wasm2.Trace.TableBytes
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.br_table {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {jumpTables emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals
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
    StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions returns locals
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
end Itasca.Runtime.Code
