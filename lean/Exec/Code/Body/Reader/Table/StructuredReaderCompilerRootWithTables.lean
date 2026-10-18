import Exec.Code.Body.Reader.Table.StructuredReaderCompilerStateWithTables
import Exec.Code.Body.Control.Table.StructuredCompiledBodyWithTables
import Exec.Code.Body.Control.Table.StructuredCompilerPrefixFinishWithTables
import Exec.Code.Body.Reader.Control.ReaderControlBoundary
import Exec.Code.Local.Source.TypedRunClosed
import Exec.Code.Body.Reader.Common.ReaderStacks
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWithTablesWasm2.finish_root {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after final : runtime.compiler.FunctionCompiler A}
    {emit types functions locals data env ctx index ft st current savedCurrent source}
    (state : StructuredReaderCompilerStateWithTablesWasm2 jumpTables emit initial before types functions (ft.results.val.map Translate.valueType) locals
      data env ctx.locals index ft st [] current [] savedCurrent)
    (root : savedCurrent.form = .body)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (encodedBody : Wasm2.BodyEncoding data source)
    (byte : data.val[st.core.pos.val]'inbounds = 0x0b#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 0x0b#u8 before = .ok (.Ok (), out, after))
    (rest : TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx index out after final) :
    StructuredCompiledBodyWithTables jumpTables emit initial final types functions (ft.results.val.map Translate.valueType) locals source := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨callback, read, encoded, realizes, zipper, afterState⟩ := reader_end_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  obtain ⟨C, outer, spine, header, base, typed, controls, blocks, vals⟩ := state.boundary.opened
  have outerEq : outer = [] := by simpa using wasm2_spine_values spine
  have rawEq : st.core.vals.val = savedCurrent.vals := by simpa [outerEq] using vals
  have savedType : savedCurrent.bt = .TypeIndex index := by
    simpa [Wasm2.Frames.bodyType] using state.boundary.bodyType
  have outs : savedCurrent.outs = ft.results.val := by
    have outputs := header.outputs
    simpa [savedType, Wasm2.outputs, Wasm2.resolve, state.boundary.signature] using outputs.symm
  have sourceForm : current.form = .body := by
    have matching := state.sources.current.form
    generalize formEq : current.form = f at matching
    rw [root] at matching
    cases matching
    rfl
  have front : current.front = [] := by simpa [Sequence.stackTypes] using state.fronts.current
  have params : current.params = [] := by simpa [root, Wasm2.Frames.Form.params] using state.sources.current.params
  have results : current.results = ft.results.val.map Translate.valueType := by simpa [outs] using state.sources.current.results
  have stack : before.reachable = true → Sequence.stackTypes st.core.vals.val = ft.results.val.map Translate.valueType := by
    intro live
    have concrete : ConcreteStack savedCurrent.vals := rawEq ▸ (state.compiled.known live)
    have mono := state.reach.current live
    have actual : Sequence.Realizes false savedCurrent.vals (savedCurrent.outs.map Translate.valueType) := by
      simpa [p, ReaderBoundaryWasm2.pending, mono] using realizes
    have decoded := realized_concrete_types concrete actual
    simpa [rawEq, outs] using decoded.symm
  have closed : out.blocks.val = [] := by
    have generic := code.end_frame.sound _ env false [] [] savedCurrent.ctrl savedCurrent.bt savedCurrent.ins savedCurrent.outs
      [] savedCurrent.vals (by simpa [p, ReaderBoundaryWasm2.pending] using controls)
      (by simpa [p, ReaderBoundaryWasm2.pending] using blocks) (by simp)
      (by simp [rawEq]) (by simpa [outerEq] using base)
      header.inputs header.outputs p.opened.shape.core
    have erased : code.end_frame {core := {st.core with pos := next}} env false = .ok (.Ok (), out) := by
      simp [code.end_frame, read, core.result.Result.Insts.CoreOpsTry.branch]
    rw [erased, WP.spec_ok] at generic
    exact (generic rfl).2.2.2.2.1
  obtain ⟨finalEq, finished⟩ := rest.closed closed
  subst final
  have complete : out.core.pos.val = data.length := by simpa using congrArg UScalar.val finished
  have sourceEq : current.source = source := state.sources.current.source.trans
    (reader_root_end_source_wasm2 p root encoded zipper complete encodedBody)
  have consumed : st.core.pos.val < out.core.pos.val := by have := encoded.span; omega
  have entry := state.compiled.entryChain.root_entered rfl
  have result := state.compiled.finish_body ops law entry stack sourceForm front params results out.core
    savedCurrent.ctrl.kind savedCurrent.bt (by omega) consumed (by omega) callback
  simpa only [StructuredCompiledBodyWithTables, sourceEq] using result

theorem StructuredReaderCompilerStateWithTablesWasm1.finish_root {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after final : runtime.compiler.FunctionCompiler A}
    {emit types functions locals data env ctx bodyBt st current savedCurrent source}
    (state : StructuredReaderCompilerStateWithTablesWasm1 jumpTables emit initial before types functions (ctx.results.val.map Translate.valueType) locals
      data env ctx bodyBt st [] current [] savedCurrent)
    (root : savedCurrent.form = .body)
    (bodyResults : Control.resultTypes bodyBt = ctx.results.val.map Translate.valueType)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (encodedBody : Wasm1.BodyEncoding data source)
    (byte : data.val[st.pos.val]'inbounds = 0x0b#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx 0x0b#u8 before = .ok (.Ok (), out, after))
    (rest : TypedRunWasm1 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx bodyBt out after final) :
    StructuredCompiledBodyWithTables jumpTables emit initial final types functions (ctx.results.val.map Translate.valueType) locals source := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨callback, read, encoded, realizes, zipper, afterState⟩ := reader_end_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out
    (by simpa only [p, ReaderBoundaryWasm1.pending, global_simps] using byte)
    (by simpa only [global_simps] using accepted)
  obtain ⟨C, outer, spine, header, base, typed, controls, vals⟩ := state.boundary.opened
  have outerEq : outer = [] := by simpa using wasm1_spine_values spine
  have rawEq : st.vals.val = savedCurrent.vals := by simpa [outerEq] using vals
  have savedType : savedCurrent.ctrl.block_type = bodyBt := by
    simpa [Wasm1.Frames.bodyType] using state.boundary.bodyType
  have sourceForm : current.form = .body := by
    have matching := state.sources.current.form
    generalize formEq : current.form = f at matching
    rw [root] at matching
    cases matching
    rfl
  have front : current.front = [] := by simpa [Sequence.stackTypes] using state.fronts.current
  have params : current.params = [] := state.sources.current.params
  have results : current.results = ctx.results.val.map Translate.valueType := by
    simpa [savedType, bodyResults] using state.sources.current.results
  have stack : before.reachable = true → Sequence.stackTypes st.vals.val = ctx.results.val.map Translate.valueType := by
    intro live
    have concrete : ConcreteStack savedCurrent.vals := rawEq ▸ (state.compiled.known live)
    have mono := state.reach.current live
    have actual : Sequence.Realizes false savedCurrent.vals (Control.resultTypes savedCurrent.ctrl.block_type) := by
      simpa [p, ReaderBoundaryWasm1.pending, mono] using realizes
    have decoded := realized_concrete_types concrete actual
    simpa [rawEq, savedType, bodyResults] using decoded.symm
  have closed : out.ctrls.val = [] := by
    have effect := code.read_end.realizes {st with pos := next} [] savedCurrent.ctrl [] savedCurrent.vals
      (by simpa using controls) (by simp [rawEq]) (by simpa [outerEq] using base)
      (Nat.le_of_lt p.val_capacity)
    rw [read, WP.spec_ok] at effect
    obtain ⟨_, _, _, controls, _⟩ := effect
    exact controls
  obtain ⟨finalEq, finished⟩ := rest.closed closed
  subst final
  have complete : out.pos.val = data.length := by simpa using congrArg UScalar.val finished
  have sourceEq : current.source = source := state.sources.current.source.trans
    (reader_root_end_source_wasm1 p root encoded zipper complete encodedBody)
  have consumed : st.pos.val < out.pos.val := by have := encoded.span; omega
  have entry := state.compiled.entryChain.root_entered rfl
  have result := state.compiled.finish_body ops law entry stack sourceForm front params results out
    savedCurrent.ctrl.kind (Control.signature savedCurrent.ctrl.block_type) (by omega) consumed (by omega) callback
  simpa only [StructuredCompiledBodyWithTables, sourceEq] using result

theorem StructuredReaderCompilerStateWithTablesWasm1.root_scopes {jumpTables : List U32} {A : Type}
    {initial before : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWithTablesWasm1 jumpTables emit initial before types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (root : savedCurrent.form = .body) : parents = [] ∧ savedParents = [] := by
  obtain ⟨C, outer, spine, _⟩ := state.boundary.opened
  rw [root] at spine
  have saved := spine.body.1
  have paired := state.sources.parents
  rw [saved] at paired
  cases paired
  exact ⟨rfl, saved⟩

theorem StructuredReaderCompilerStateWithTablesWasm2.root_scopes {jumpTables : List U32} {A : Type}
    {initial before : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env sourceLocals index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWithTablesWasm2 jumpTables emit initial before types functions returns locals data env sourceLocals index ft st
      parents current savedParents savedCurrent)
    (root : savedCurrent.form = .body) : parents = [] ∧ savedParents = [] := by
  obtain ⟨C, outer, spine, _⟩ := state.boundary.opened
  rw [root] at spine
  have saved := spine.body.1
  have paired := state.sources.parents
  rw [saved] at paired
  cases paired
  exact ⟨rfl, saved⟩
end Exec.Code
