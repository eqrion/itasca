import Itasca.Runtime.Compiler.Body.Relations.Entry.PreparedRawInitial
import Itasca.Runtime.Compiler.Body.Reader.Replay.SafetyAndFinish
import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableScratchEntry

open WebAssembly

open Itasca.Representation

/-!
Initial reader/compiler and compiler-table certificates for a prepared function entry.
-/

/-! ## Prepared Reader Initial -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
theorem indexed_prepared_compiler_start (jumpTables : List U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial started : runtime.compiler.FunctionCompiler A} {data env index start }
    (w : CodeEntry.Prepared data env index start )
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translation.valueType)))
    (endFits : batchStart.val + w.finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (startedCall : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial w.ctx w.typeIdx w.bodyStart w.finish = .ok (.Ok (),started)) :
    CompilerEntryFacts started env w.ctx w.typeIdx w.ft w.body ∧
    StructuredCompilerPrefix jumpTables emit started started
      (env.types.val.map Translation.Environment.funcType) (env.func_types.val.map Translation.Environment.funcType)
      (w.ft.results.val.map Translation.valueType) (w.ctx.locals.val.map Translation.valueType)
      [] (SourceScope.initial (w.ft.results.val.map Translation.valueType)) [] 0 := by
  have sourceLookup : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt, w.function_type]
  obtain ⟨signature, lookup, matched⟩ := signatureTable.lookup_source sourceLookup
  have beginFits : batchStart.val + w.bodyStart.val ≤ Usize.max := by
    have length := w.body_bytes.length
    omega
  have facts := compiler_function_start_facts ops law signatures functionSlots budget batchStart initial started
    w.ctx w.typeIdx signature w.bodyStart w.finish lookup beginFits endFits created startedCall
  obtain ⟨layout, locals, capacity, params, typeIndex, bodyStart, _, sigs, funcs, _⟩ := facts
  constructor
  · refine ⟨layout, locals, capacity, ?_, typeIndex, ?_, ?_, ?_⟩
    · rw [params]
      exact matched.paramWords
    · simpa only [sigs] using signatureTable
    · simpa only [FunctionParameterSlots, funcs] using functionTable
    · exact function_body_coordinate_bound w.body_bytes bodyStart endFits
  · exact structured_compiler_function_start_prefix emit ops law signatures functionSlots budget batchStart initial started
      w.ctx w.typeIdx signature w.bodyStart w.finish _ _ _ lookup matched.resultWords beginFits endFits created startedCall

theorem indexed_prepared_compiler_initial (jumpTables : List U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial started : runtime.compiler.FunctionCompiler A} {data env index start }
    (w : CodeEntry.Prepared data env index start )
    (bodyBound : w.body.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translation.valueType)))
    (endFits : batchStart.val + w.finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (startedCall : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial w.ctx w.typeIdx w.bodyStart w.finish = .ok (.Ok (),started)) :
    CompilerEntryFacts started env w.ctx w.typeIdx w.ft w.body ∧
    StructuredReaderCompilerPoint jumpTables emit started started
      (env.types.val.map Translation.Environment.funcType) (env.func_types.val.map Translation.Environment.funcType)
      (w.ft.results.val.map Translation.valueType) (w.ctx.locals.val.map Translation.valueType)
      w.body env w.ctx.locals w.typeIdx w.ft (Body.initial w.typeIdx) := by
  obtain ⟨facts, compiled⟩ := indexed_prepared_compiler_start jumpTables emit ops law w signatureTable functionTable endFits created startedCall
  have lookup : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt, w.function_type]
  exact ⟨facts, (StructuredReaderCompilerState.initial _ _ _ _ _ _ _ _ _ lookup bodyBound compiled).point⟩

end Itasca.Compiler

end

/-! ## Prepared Table Initial -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem prepared_compiler_table_boundary {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial started : runtime.compiler.FunctionCompiler A} {data env index start }
    (w : CodeEntry.Prepared data env index start )
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart=.ok initial)
    (startedCall : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial w.ctx w.typeIdx w.bodyStart w.finish = .ok (.Ok (),started)) :
    CompilerTableBoundary started := by
  have boundary := compiler_new_table_boundary ops signatures functionSlots budget batchStart
  rw [created,WP.spec_ok] at boundary
  exact compiler_function_start_table_boundary ops law initial started w.ctx w.typeIdx w.bodyStart w.finish
    (.Ok ()) boundary startedCall

theorem indexed_table_prepared_compiler_initial
    (emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial started : runtime.compiler.FunctionCompiler A} {data env index start }
    (w : CodeEntry.Prepared data env index start )
    (bodyBound : w.body.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val)=
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translation.valueType)))
    (endFits : batchStart.val+w.finish.val≤Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart=.ok initial)
    (startedCall : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial w.ctx w.typeIdx w.bodyStart w.finish = .ok (.Ok (),started)) :
    CompilerEntryFacts started env w.ctx w.typeIdx w.ft w.body ∧
    IndexedTableReaderCompilerPoint emit started started
      (env.types.val.map Translation.Environment.funcType) (env.func_types.val.map Translation.Environment.funcType)
      (w.ft.results.val.map Translation.valueType) (w.ctx.locals.val.map Translation.valueType)
      w.body env w.ctx.locals w.typeIdx w.ft (Body.initial w.typeIdx) := by
  have all := fun more : CompilerTables => indexed_prepared_compiler_initial
    ((CompilerTables.ofFunction started.function).append more).jumpTables
    (emit ((CompilerTables.ofFunction started.function).append more))
    ops law w bodyBound signatureTable functionTable endFits created startedCall
  exact ⟨(all .empty).1,⟨prepared_compiler_table_boundary ops law w created startedCall,fun more => (all more).2⟩⟩

end Itasca.Compiler

end
