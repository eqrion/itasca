import Exec.Code.Body.Reader.Table.StructuredReaderPrefixElseEnteredWithTables
import Exec.Code.Local.Relations.Control.KnownControlStack
import Exec.Code.Body.Reader.Common.ReaderReachabilitySteps
import Exec.Code.Body.Reader.Control.ReaderScopeFronts
import Exec.Code.Body.Reader.Control.ReaderControlBoundary
import Exec.Code.Body.Reader.Common.ReaderKnownFronts
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem structured_reader_prefix_else_entered_wasm1_with_tables {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.vals.val p.start.val)
    (same : ReaderScopeZipperWasm1 parents current p.parents p.current)
    (reach : ReaderReachabilityWasm1 before.reachable parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm1.Frames.Saved.vals))
    (savedKnown : ReaderKnownFronts parents current (p.parents.map Wasm1.Frames.Saved.vals))
    (initialLocals : LocalLayout initial) (entered : current.entered = true)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_ELSE)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_ELSE before = .ok (.Ok (), out, after)) :
    ∃ condition noEntry,
      current.form = .then_ (Control.blockType p.current.ctrl.block_type) condition ∧
      noEntry.val = before.function.code.val.length + (if before.reachable then 1 else 0) ∧
      let next := current.begin_else (Control.blockType p.current.ctrl.block_type) condition before.function.code.val.length noEntry before.reachable
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
  have outerKnown : ConcreteStack outer := by
    rw [wasm1_spine_values spine]
    simpa only [List.flatMap_def] using savedKnown.current entered
  have known := wasm1_else_concrete st out _ _ outer p.current.vals p.current.ctrl.block_type ctrls vals base outerKnown read
  have frontEq : current.front = Sequence.stackTypes outer := by
    rw [wasm1_spine_values spine]
    simpa only [List.flatMap_def] using fronts.current
  have stack : before.reachable = true → Sequence.stackTypes st.vals.val = current.front ++ current.results := by
    intro live
    have segmentKnown : ConcreteStack p.current.vals := (concreteStack_append.mp (vals ▸ invariant.known live)).2
    have mono := reach.current live
    have realized := results
    rw [mono] at realized
    have segmentTypes := (realized_concrete_types segmentKnown realized).symm
    simp only [vals, Sequence.stackTypes, List.map_append]
    change Sequence.stackTypes outer ++ Sequence.stackTypes p.current.vals = _
    rw [segmentTypes, ← frontEq, same.current.results]
  have sourceTypes : SourceStack out.vals.val current.input := by
    refine ⟨known, ?_⟩
    obtain ⟨C', outer', spine', header', base', typed', controls', values'⟩ := opened
    have outerTypes : Sequence.stackTypes outer' = current.front := by
      rw [wasm1_spine_values spine']
      simpa only [List.flatMap_def] using fronts.current.symm
    simp only [values', Sequence.stackTypes, List.map_append]
    change Sequence.stackTypes outer' ++ Sequence.stackTypes p.current.nextElse.vals = current.input
    rw [outerTypes]
    simp [Wasm1.Frames.Saved.nextElse, SourceScope.input, same.current.params, Sequence.stackTypes]
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
  obtain ⟨noEntry, positionEq, certified⟩ := structured_callback_else_entered_prefix_with_tables ops law initial before after types functions returns locals
    parents current st.vals.val p.start.val invariant initialLocals entered out (Control.signature p.current.ctrl.block_type)
    (Control.blockType p.current.ctrl.block_type) condition form stack sourceTypes sourceBound consumed callback
  exact ⟨condition, noEntry, form, positionEq, certified,
    same.begin_else _ condition form before.function.code.val.length noEntry before.reachable,
    reach.begin_else after.reachable _ condition before.function.code.val.length noEntry before.reachable,
    fronts.begin_else _ condition before.function.code.val.length noEntry before.reachable,
    reader_else_boundary_wasm1 p sourceForm encoded opened afterState, afterState⟩
end Exec.Code
