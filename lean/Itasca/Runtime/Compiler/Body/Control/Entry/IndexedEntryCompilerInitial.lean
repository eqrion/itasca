import Itasca.Runtime.Compiler.Body.Relations.Entry.EntryCompilerInitial
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedCompilerInitial
import Itasca.Runtime.Compiler.Body.Reader.Replay.StructuredPoint

/-!
Initial indexed compiler certificates from validated entries.

Main declarations: `indexed_witness_compiler_start` and `indexed_witness_compiler_initial_wasm2`. A direct consumer is `Compiler.Body.Control.Table.IndexedTableEntryInitial`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
theorem indexed_witness_compiler_start (jumpTables : List U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish profile}
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final profile)
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    (endFits : batchStart.val + finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial) :
    CompilerEntryFacts w.startedState env w.ctx w.typeIdx w.ft w.body ∧
    StructuredCompilerPrefix jumpTables emit w.startedState w.startedState
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (w.ft.results.val.map Translate.valueType) (w.ctx.locals.val.map Translate.valueType)
      [] (SourceScope.initial (w.ft.results.val.map Translate.valueType)) [] 0 := by
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

theorem indexed_witness_compiler_initial_wasm2 (jumpTables : List U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish profile}
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final profile)
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    (endFits : batchStart.val + finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial) :
    CompilerEntryFacts w.startedState env w.ctx w.typeIdx w.ft w.body ∧
    StructuredReaderCompilerPointWasm2 jumpTables emit w.startedState w.startedState
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (w.ft.results.val.map Translate.valueType) (w.ctx.locals.val.map Translate.valueType)
      w.body env w.ctx.locals w.typeIdx w.ft (Wasm2.initial w.typeIdx) ∧
    TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      w.body env w.ctx w.typeIdx (Wasm2.initial w.typeIdx) w.startedState final := by
  obtain ⟨facts, compiled⟩ := indexed_witness_compiler_start jumpTables emit ops law w signatureTable functionTable endFits created
  have run := witness_typed_steps w
  have lookup : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt, w.function_type]
  exact ⟨facts, (StructuredReaderCompilerStateWasm2.initial _ _ _ _ _ _ _ _ _ lookup run.body_size compiled).point, run⟩

end Itasca.Runtime.Compiler
