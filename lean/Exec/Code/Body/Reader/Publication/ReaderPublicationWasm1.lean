import Exec.Code.Body.Reader.Replay.SingleCallbackWasm1
import Exec.Code.Body.Reader.Control.ReaderEnterPublicationWasm1
import Exec.Code.Body.Reader.Control.ReaderEndPublication
import Exec.Code.Body.Reader.Table.ReaderTablePublication
import Itasca.Visitor.ReaderAcceptedProgress

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Every accepted Wasm 1 reader step preserves both publication invariants
from its source-typed reached prefix. Entry, END and table collection are
handled by their actual readers; every other byte uses the exhaustive event
adapter. No opcode-subset premise or completed code certificate is supplied. -/
theorem reader_publication_wasm1 {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop}
    {data env ctx bodyBt st} (p : Wasm1.Pending data env ctx bodyBt st)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial before types functions returns locals
      parents current st.vals.val p.start.val)
    (reach : ReaderReachabilityWasm1 before.reachable parents current p.parents p.current)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (extent : before.function.body_end.val = before.function.body_start.val+data.length)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (data.val[p.start.val]'p.inbounds) before = .ok (.Ok (),out,after)) :
    SourceCoordinates after ∧ ControlMapPublication after := by
  let opcode := data.val[p.start.val]'p.inbounds
  have afterState := p.accepted_after (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out accepted
  have consumed : p.start.val < out.pos.val := by
    have position := p.pos
    have advanced := afterState.2.1
    omega
  have inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val := by
    have cursor := invariant.cursor
    have bounded := p.inbounds
    change p.start.val < data.length at bounded
    omega
  have forward : before.next_source.val ≤ out.pos.val := le_trans invariant.cursor (Nat.le_of_lt consumed)
  by_cases opening : opcode = code.OP_BLOCK ∨ opcode = code.OP_LOOP ∨ opcode = code.OP_IF
  · exact reader_enter_publication_wasm1 p ops law initial before after out types functions returns locals parents current
      invariant reach coordinates maps extent opcode opening rfl accepted
  by_cases ending : opcode = code.OP_END
  · have call : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx code.OP_END before = .ok (.Ok (),out,after) := by simpa only [← ending] using accepted
    exact reader_end_publication_wasm1 p ops law initial before after out types functions returns locals parents current
      invariant coordinates maps extent ending call
  by_cases table : opcode = code.OP_BR_TABLE
  · have call : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx code.OP_BR_TABLE before = .ok (.Ok (),out,after) := by simpa only [← table] using accepted
    exact reader_table_publication_wasm1 ops law before after st out data env ctx coordinates maps inside forward call
  have blocked : opcode ≠ code.OP_BLOCK ∧ opcode ≠ code.OP_LOOP ∧ opcode ≠ code.OP_IF ∧
      opcode ≠ code.OP_END ∧ opcode ≠ code.OP_BR_TABLE := by tauto
  obtain ⟨action,ordinary,range,callback⟩ := reader_single_callback_wasm1
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx opcode before after out blocked accepted
  exact compiler_non_scope_hook_publication ops law before after out
    (.of_range action range ordinary) coordinates maps inside forward callback

end Exec.Code
