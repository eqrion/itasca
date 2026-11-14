import Itasca.Runtime.Compiler.Body.Reader.Replay.OrdinaryEffects
import Itasca.Runtime.Compiler.Body.Reader.Scalar.OrdinaryCompilation
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPreserved
import Itasca.Runtime.Compiler.Body.Control.Embedding.OrdinaryEmbedding
import Itasca.Runtime.Compiler.Body.Reader.Control.ControlEffects
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixStart

/-!
Sections, each formerly its own module: IndexedTablePointOrdinary, IndexedTablePointRoot.
-/

/-! ## IndexedTablePointOrdinary -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
theorem IndexedTableReaderCompilerPointWasm2.ordinary {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types locals data env ctx index ft st}
    (contextLocals : C.LOCALS = locals)
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (includeCumulative : ∀ tables, OrdinaryEmbedding tables.indirect C (emit tables))
    (point : IndexedTableReaderCompilerPointWasm2 emit initial before types (env.func_types.val.map EnvTranslation.funcType) (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft st)
    (metadata : FunctionParameterSlots initial env)
    (localsMatch : initial.function.locals = ctx.locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (opcode : U8) (ordinary : opcode ∈ readerOrdinaryOpcodes)
    (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index opcode before = .ok (.Ok (), out, after)) :
    IndexedTableReaderCompilerPointWasm2 emit initial after types (env.func_types.val.map EnvTranslation.funcType) (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have effects := reader_ordinary_effects_wasm2 p ops law before after out ctx opcode ordinary byte accepted
  apply point.preserved_step effects.tables effects.depths effects.code_mono
  intro future old
  have embedding : LinearEmbedding locals (emit ((CompilerTables.ofFunction before.function).append future)) := by
    intro input instruction code output h
    exact (includeCumulative ((CompilerTables.ofFunction before.function).append future)).scalar (.linear (by simpa only [contextLocals] using h))
  exact old.ordinary ops law embedding metadata localsMatch next advance inbounds out sourceBound bodyBound opcode ordinary byte accepted
end Itasca.Runtime.Compiler

end

/-! ## IndexedTablePointRoot -/

section

namespace Itasca.Runtime.Compiler
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
      {core := {st.core with pos := next}} data env ctx index 11#u8 before = .ok (.Ok (),out,after))
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
end Itasca.Runtime.Compiler

end
