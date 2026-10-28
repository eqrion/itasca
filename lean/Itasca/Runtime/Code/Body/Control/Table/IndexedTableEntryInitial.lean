import Itasca.Runtime.Code.Body.Control.Common.IndexedEntryCompilerInitial
import Itasca.Runtime.Code.Body.Reader.Table.IndexedTableReaderCompilerPoint
import Itasca.Runtime.Code.Local.Callbacks.Table.CompilerTableScratchEntry
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem witness_compiler_table_boundary {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish profile}
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final profile)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart=.ok initial) :
    CompilerTableBoundary w.startedState := by
  have boundary := compiler_new_table_boundary ops signatures functionSlots budget batchStart
  rw [created,WP.spec_ok] at boundary
  exact compiler_function_start_table_boundary ops law initial w.startedState w.ctx w.typeIdx w.bodyStart finish
    (.Ok ()) boundary w.function_start

theorem indexed_table_witness_compiler_initial_wasm2
    (emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish profile}
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final profile)
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val)=
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    (endFits : batchStart.val+finish.val≤Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart=.ok initial) :
    CompilerEntryFacts w.startedState env w.ctx w.typeIdx w.ft w.body ∧
    IndexedTableReaderCompilerPointWasm2 emit w.startedState w.startedState
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (w.ft.results.val.map Translate.valueType) (w.ctx.locals.val.map Translate.valueType)
      w.body env w.ctx.locals w.typeIdx w.ft (Wasm2.initial w.typeIdx) ∧
    TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      w.body env w.ctx w.typeIdx (Wasm2.initial w.typeIdx) w.startedState final := by
  have all := fun more : CompilerTables => indexed_witness_compiler_initial_wasm2
    ((CompilerTables.ofFunction w.startedState.function).append more).jumpTables
    (emit ((CompilerTables.ofFunction w.startedState.function).append more))
    ops law w signatureTable functionTable endFits created
  exact ⟨(all .empty).1,⟨witness_compiler_table_boundary ops law w created,fun more => (all more).2.1⟩,(all .empty).2.2⟩

end Itasca.Runtime.Code
