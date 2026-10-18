import Exec.Code.Body.Reader.Common.IndexedReaderCompilerBodyWasm1
import Exec.Code.Body.Reader.Common.ReaderRootEnd
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem IndexedTableReaderCompilerPointWasm1.end_or_closed {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before middle : runtime.compiler.FunctionCompiler A}
    {types functions locals data env ctx bodyBt st}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (point : IndexedTableReaderCompilerPointWasm1 emit initial before types functions (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt st)
    (initialLocals : LocalLayout initial)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.pos.val]'inbounds = 11#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx 11#u8 before = .ok (.Ok (),out,middle)) :
    out.ctrls.val = [] ∨
    IndexedTableReaderCompilerPointWasm1 emit initial middle types functions (ctx.results.val.map Translate.valueType) locals data env ctx bodyBt out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have pairs := reader_end_tables_wasm1 p ops law before middle out byte accepted
  have depths := reader_end_depths_wasm1 p ops law before middle out byte accepted
  have growth := reader_end_code_mono_wasm1 p ops law before middle out byte accepted
  by_cases closed : out.ctrls.val = []
  · exact .inl closed
  · apply Or.inr
    apply point.preserved_step pairs depths growth
    intro future old
    obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
    have root : savedCurrent.form ≠ .body := by
      intro root
      obtain ⟨rfl,rfl⟩ := state.root_scopes root
      let p := state.boundary.pending next advance inbounds
      obtain ⟨_,read,_,_,_,afterState⟩ := reader_end_wasm1 p
        (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before middle out
        (by simpa only [p,ReaderBoundaryWasm1.pending,global_simps] using byte) (by simpa only [global_simps] using accepted)
      obtain ⟨C,outer,spine,header,base,typed,controls,vals⟩ := state.boundary.opened
      have outerEq : outer = [] := by simpa using wasm1_spine_values spine
      have rawEq : st.vals.val = savedCurrent.vals := by simpa [outerEq] using vals
      have effect := code.read_end.realizes {st with pos := next} [] savedCurrent.ctrl [] savedCurrent.vals
        (by simpa using controls) (by simp [rawEq]) (by simpa [outerEq] using base)
        (Nat.le_of_lt p.val_capacity)
      rw [read,WP.spec_ok] at effect
      exact closed effect.2.2.2.1
    exact state.end_nested ops law initialLocals next advance inbounds out root bodyBound
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
end Exec.Code
