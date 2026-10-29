import Itasca.Runtime.Compiler.Body.Reader.Control.ControlEffects
import Itasca.Runtime.Compiler.Body.Control.Table.IndexedTablePointControl
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem IndexedTableReaderCompilerPointWasm2.finish_root {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after final : runtime.compiler.FunctionCompiler A}
    {types functions locals data env ctx index ft st source}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial before types functions
      (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft st)
    (root : st.blocks.val.length = 1)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (encodedBody : Wasm2.BodyEncoding data source)
    (byte : data.val[st.core.pos.val]'inbounds = 11#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 11#u8 before = .ok (.Ok (),out,after))
    (rest : TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx index out after final) :
    StructuredCompiledBody final.function.jump_tables.val (emit (CompilerTables.ofFunction final.function)) initial final types functions
      (ft.results.val.map Translate.valueType) locals source := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  have rootForm := state.boundary.root_iff.mpr root
  obtain ⟨rfl,rfl⟩ := state.root_scopes rootForm
  let p := state.boundary.pending next advance inbounds
  have effects := reader_end_effects_wasm2 ops law before after _ out data env ctx _ (by simpa only [global_simps] using accepted)
  have pairs := effects.tables
  obtain ⟨callback,read,encoded,realizes,zipper,afterState⟩ := reader_end_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  obtain ⟨sourceC,outer,spine,header,base,typed,controls,blocks,vals⟩ := state.boundary.opened
  have outerEq : outer = [] := by simpa using wasm2_spine_values spine
  have rawEq : st.core.vals.val = savedCurrent.vals := by simpa [outerEq] using vals
  have closed : out.blocks.val = [] := by
    have generic := code.end_frame.sound _ env false [] [] savedCurrent.ctrl savedCurrent.bt savedCurrent.ins savedCurrent.outs
      [] savedCurrent.vals (by simpa [p,ReaderBoundaryWasm2.pending] using controls)
      (by simpa [p,ReaderBoundaryWasm2.pending] using blocks) (by simp)
      (by simp [rawEq]) (by simpa [outerEq] using base)
      header.inputs header.outputs p.opened.shape.core
    have erased : code.end_frame {core := {st.core with pos := next}} env false = .ok (.Ok (),out) := by
      simp [code.end_frame,read,core.result.Result.Insts.CoreOpsTry.branch]
    rw [erased,WP.spec_ok] at generic
    exact (generic rfl).2.2.2.2.1
  obtain ⟨rfl,finished⟩ := rest.closed closed
  have complete := state.finish_root ops law rootForm next advance inbounds out sourceBound bodyBound encodedBody byte accepted rest
  change StructuredCompiledBody (CompilerTables.ofFunction final.function).jumpTables
    (emit (CompilerTables.ofFunction final.function)) initial final types functions
    (ft.results.val.map Translate.valueType) locals source
  simpa only [pairs,CompilerTables.append_empty] using complete
end Itasca.Runtime.Code
