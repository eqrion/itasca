import Exec.Code.Body.Reader.Table.StructuredReaderPrefixElseDormantWithTables
import Exec.Code.Local.Relations.Control.KnownControlStack
import Exec.Code.Body.Reader.Common.ReaderReachabilitySteps
import Exec.Code.Body.Reader.Control.ReaderScopeFronts
import Exec.Code.Body.Reader.Control.ReaderControlBoundary
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem structured_reader_prefix_else_dormant_wasm1_with_tables {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.vals.val p.start.val)
    (same : ReaderScopeZipperWasm1 parents current p.parents p.current)
    (reach : ReaderReachabilityWasm1 before.reachable parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm1.Frames.Saved.vals))
    (unentered : current.entered = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_ELSE)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_ELSE before = .ok (.Ok (), out, after)) :
    ∃ condition noEntry,
      current.form = .then_ (Control.blockType p.current.ctrl.block_type) condition ∧
      noEntry.val = before.function.code.val.length ∧
      let next := current.begin_else (Control.blockType p.current.ctrl.block_type) condition noEntry.val noEntry false
      StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial after types functions returns locals parents next out.vals.val out.pos.val ∧
      ReaderScopeZipperWasm1 parents next p.parents p.current.nextElse ∧
      ReaderReachabilityWasm1 after.reachable parents next p.parents p.current.nextElse ∧
      ReaderScopeFronts parents next (p.parents.map Wasm1.Frames.Saved.vals) ∧
      ReaderBoundaryWasm1 data env ctx bodyBt out p.parents p.current.nextElse ∧ p.After out := by
  obtain ⟨callback, read, sourceForm, encoded, results, opened, afterState⟩ := reader_else_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out byte accepted
  have matched := same.current.form
  rw [sourceForm] at matched
  have sourceThen : ∃ condition, current.form = .then_ (Control.blockType p.current.ctrl.block_type) condition := by
    generalize currentForm : current.form = scopeForm at matched
    cases matched with
    | then_ condition => exact ⟨condition, rfl⟩
  obtain ⟨condition, form⟩ := sourceThen
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := p.opened
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES, limits.MAX_MODULE_BYTES] at size ⊢
    omega
  have consumed : p.start.val < out.pos.val := by
    have position := p.pos
    have advanced := afterState.2.1
    omega
  obtain ⟨noEntry, positionEq, certified⟩ := structured_callback_else_dormant_prefix_with_tables ops law initial before after types functions returns locals
    parents current st.vals.val p.start.val invariant unentered out (Control.signature p.current.ctrl.block_type)
    (Control.blockType p.current.ctrl.block_type) condition form  sourceBound consumed callback
  exact ⟨condition, noEntry, form, positionEq, certified,
    same.begin_else _ condition form noEntry.val noEntry false,
    reach.begin_else after.reachable _ condition noEntry.val noEntry false,
    fronts.begin_else _ condition noEntry.val noEntry false,
    reader_else_boundary_wasm1 p sourceForm encoded opened afterState, afterState⟩
end Exec.Code
