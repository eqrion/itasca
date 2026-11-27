import Itasca.Runtime.Compiler.Body.Relations.Entry.PreparedRawInitial
import Itasca.Runtime.Compiler.Body.Reader.Replay.SafetyAndFinish
import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableScratchEntry
import Itasca.Runtime.Compiler.Body.Reader.Replay.OrdinaryEffects
import Itasca.Runtime.Compiler.Body.Reader.Scalar.OrdinaryCompilation
import Itasca.Runtime.Compiler.Body.Control.BranchesAndDormantEntry
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchAndScopeEffects
import Itasca.Runtime.Compiler.Body.Control.ControlPointsAndInitialPrefixes

open WebAssembly

/-!
Proofs for Runtime / Compiler / Body / Control.

This module collects IndexedEntryCompilerInitial, PointRoot.
Each section documents its contracts and consumers.
-/

/-! ## IndexedEntryCompilerInitial -/

section

/-!
Proofs for Runtime / Compiler / Body / Control.

This module collects IndexedEntryCompilerInitial, EntryInitial.
Each section documents its contracts and consumers.
-/

/-! ## IndexedEntryCompilerInitial -/

section

open Itasca.Representation

/-!
Initial indexed compiler certificates from validated entries.

Main declarations: `indexed_witness_compiler_start` and `indexed_witness_compiler_initial`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
theorem indexed_witness_compiler_start (jumpTables : List U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish }
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final )
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translation.valueType)))
    (endFits : batchStart.val + finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial) :
    CompilerEntryFacts w.startedState env w.ctx w.typeIdx w.ft w.body ∧
    StructuredCompilerPrefix jumpTables emit w.startedState w.startedState
      (env.types.val.map Translation.Environment.funcType) (env.func_types.val.map Translation.Environment.funcType)
      (w.ft.results.val.map Translation.valueType) (w.ctx.locals.val.map Translation.valueType)
      [] (SourceScope.initial (w.ft.results.val.map Translation.valueType)) [] 0 := by
  have sourceLookup : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt, w.function_type]
  obtain ⟨signature, lookup, matched⟩ := signatureTable.lookup_source sourceLookup
  have beginFits : batchStart.val + w.bodyStart.val ≤ Usize.max := by
    have length := w.body_bytes.length
    omega
  have facts := compiler_function_start_facts ops law signatures functionSlots budget batchStart initial w.startedState
    w.ctx w.typeIdx signature w.bodyStart finish lookup beginFits endFits created w.function_start
  obtain ⟨layout, locals, capacity, params, typeIndex, bodyStart, _, sigs, funcs, _⟩ := facts
  constructor
  · refine ⟨layout, locals, capacity, ?_, typeIndex, ?_, ?_, ?_⟩
    · rw [params]
      exact matched.paramWords
    · simpa only [sigs] using signatureTable
    · simpa only [FunctionParameterSlots, funcs] using functionTable
    · exact function_body_coordinate_bound w.body_bytes bodyStart endFits
  · exact structured_compiler_function_start_prefix emit ops law signatures functionSlots budget batchStart initial w.startedState
      w.ctx w.typeIdx signature w.bodyStart finish _ _ _ lookup matched.resultWords beginFits endFits created w.function_start

theorem indexed_witness_compiler_initial (jumpTables : List U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish }
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final )
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translation.valueType)))
    (endFits : batchStart.val + finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial) :
    CompilerEntryFacts w.startedState env w.ctx w.typeIdx w.ft w.body ∧
    StructuredReaderCompilerPoint jumpTables emit w.startedState w.startedState
      (env.types.val.map Translation.Environment.funcType) (env.func_types.val.map Translation.Environment.funcType)
      (w.ft.results.val.map Translation.valueType) (w.ctx.locals.val.map Translation.valueType)
      w.body env w.ctx.locals w.typeIdx w.ft (Body.initial w.typeIdx) ∧
    TypedRun (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      w.body env w.ctx w.typeIdx (Body.initial w.typeIdx) w.startedState final := by
  obtain ⟨facts, compiled⟩ := indexed_witness_compiler_start jumpTables emit ops law w signatureTable functionTable endFits created
  have run := witness_typed_steps w
  have lookup : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt, w.function_type]
  exact ⟨facts, (StructuredReaderCompilerState.initial _ _ _ _ _ _ _ _ _ lookup run.body_size compiled).point, run⟩

end Itasca.Compiler

end

/-! ## EntryInitial -/

section

open Itasca.Representation

/-!
# Initial branch-table entry state

An entry witness supplies the compiler's branch-table boundary and the initial indexed reader relation. This joins framed input with structured body compilation.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem witness_compiler_table_boundary {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish }
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final )
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart=.ok initial) :
    CompilerTableBoundary w.startedState := by
  have boundary := compiler_new_table_boundary ops signatures functionSlots budget batchStart
  rw [created,WP.spec_ok] at boundary
  exact compiler_function_start_table_boundary ops law initial w.startedState w.ctx w.typeIdx w.bodyStart finish
    (.Ok ()) boundary w.function_start

theorem indexed_table_witness_compiler_initial
    (emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish }
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final )
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val)=
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translation.valueType)))
    (endFits : batchStart.val+finish.val≤Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart=.ok initial) :
    CompilerEntryFacts w.startedState env w.ctx w.typeIdx w.ft w.body ∧
    IndexedTableReaderCompilerPoint emit w.startedState w.startedState
      (env.types.val.map Translation.Environment.funcType) (env.func_types.val.map Translation.Environment.funcType)
      (w.ft.results.val.map Translation.valueType) (w.ctx.locals.val.map Translation.valueType)
      w.body env w.ctx.locals w.typeIdx w.ft (Body.initial w.typeIdx) ∧
    TypedRun (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      w.body env w.ctx w.typeIdx (Body.initial w.typeIdx) w.startedState final := by
  have all := fun more : CompilerTables => indexed_witness_compiler_initial
    ((CompilerTables.ofFunction w.startedState.function).append more).jumpTables
    (emit ((CompilerTables.ofFunction w.startedState.function).append more))
    ops law w signatureTable functionTable endFits created
  exact ⟨(all .empty).1,⟨witness_compiler_table_boundary ops law w created,fun more => (all more).2.1⟩,(all .empty).2.2⟩

end Itasca.Compiler

end

end

/-! ## PointRoot -/

section

/-!
# Point Root

Ordinary instruction points and root boundaries connect indexed reader execution to compiler state. Root characterization supplies the boundary used by complete function compilation.
-/

/-! ## IndexedTablePointOrdinary -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
theorem IndexedTableReaderCompilerPoint.ordinary {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types locals data env ctx index ft st}
    (contextLocals : C.LOCALS = locals)
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (includeCumulative : ∀ tables, OrdinaryEmbedding tables.indirect C (emit tables))
    (point : IndexedTableReaderCompilerPoint emit initial before types (env.func_types.val.map Translation.Environment.funcType) (ft.results.val.map Translation.valueType) locals data env ctx.locals index ft st)
    (metadata : FunctionParameterSlots initial env)
    (localsMatch : initial.function.locals = ctx.locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (opcode : U8) (ordinary : opcode ∈ readerOrdinaryOpcodes)
    (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index opcode before = .ok (.Ok (), out, after)) :
    IndexedTableReaderCompilerPoint emit initial after types (env.func_types.val.map Translation.Environment.funcType) (ft.results.val.map Translation.valueType) locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have effects := reader_ordinary_effects p ops law before after out ctx opcode ordinary byte accepted
  apply point.preserved_step effects.tables effects.depths effects.code_mono
  intro future old
  have embedding : LinearEmbedding locals (emit ((CompilerTables.ofFunction before.function).append future)) := by
    intro input instruction code output h
    exact (includeCumulative ((CompilerTables.ofFunction before.function).append future)).scalar (.linear (by simpa only [contextLocals] using h))
  exact old.ordinary ops law embedding metadata localsMatch next advance inbounds out sourceBound bodyBound opcode ordinary byte accepted
end Itasca.Compiler

end

/-! ## IndexedTablePointRoot -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem IndexedTableReaderCompilerPoint.finish_root {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after final : runtime.compiler.FunctionCompiler A}
    {types functions locals data env ctx index ft st source}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (point : IndexedTableReaderCompilerPoint emit initial before types functions
      (ft.results.val.map Translation.valueType) locals data env ctx.locals index ft st)
    (root : st.blocks.val.length = 1)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (encodedBody : Body.BodyEncoding data source)
    (byte : data.val[st.core.pos.val]'inbounds = 11#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index 11#u8 before = .ok (.Ok (),out,after))
    (rest : TypedRun (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx index out after final) :
    StructuredCompiledBody final.function.jump_tables.val (emit (CompilerTables.ofFunction final.function)) initial final types functions
      (ft.results.val.map Translation.valueType) locals source := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  have rootForm := state.boundary.root_iff.mpr root
  obtain ⟨rfl,rfl⟩ := state.root_scopes rootForm
  let p := state.boundary.pending next advance inbounds
  have effects := reader_end_effects ops law before after _ out data env ctx _ (by simpa only [global_simps] using accepted)
  have pairs := effects.tables
  obtain ⟨callback,read,encoded,realizes,zipper,afterState⟩ := reader_end p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  obtain ⟨sourceC,outer,spine,header,base,typed,controls,blocks,vals⟩ := state.boundary.opened
  have outerEq : outer = [] := by simpa using spine_values spine
  have rawEq : st.core.vals.val = savedCurrent.vals := by simpa [outerEq] using vals
  have closed : out.blocks.val = [] := by
    have generic := code.end_frame.sound _ env false [] [] savedCurrent.ctrl savedCurrent.bt savedCurrent.ins savedCurrent.outs
      [] savedCurrent.vals (by simpa [p,ReaderBoundary.pending] using controls)
      (by simpa [p,ReaderBoundary.pending] using blocks) (by simp)
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
    (ft.results.val.map Translation.valueType) locals source
  simpa only [pairs,CompilerTables.append_empty] using complete
end Itasca.Compiler

end

end
