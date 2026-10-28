import Exec.Code.Body.Reader.Common.PreparedReaderInitial
import Exec.Code.Body.Reader.Table.IndexedTableReaderCompilerPoint
import Exec.Code.Local.Callbacks.Table.CompilerTableScratchEntry
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem prepared_compiler_table_boundary {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial started : runtime.compiler.FunctionCompiler A} {data env index start profile}
    (w : CodeEntry.Prepared data env index start profile)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart=.ok initial)
    (startedCall : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial w.ctx w.typeIdx w.bodyStart w.finish = .ok (.Ok (),started)) :
    CompilerTableBoundary started := by
  have boundary := compiler_new_table_boundary ops signatures functionSlots budget batchStart
  rw [created,WP.spec_ok] at boundary
  exact compiler_function_start_table_boundary ops law initial started w.ctx w.typeIdx w.bodyStart w.finish
    (.Ok ()) boundary startedCall

theorem indexed_table_prepared_compiler_initial_wasm2
    (emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial started : runtime.compiler.FunctionCompiler A} {data env index start profile}
    (w : CodeEntry.Prepared data env index start profile)
    (bodyBound : w.body.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val)=
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    (endFits : batchStart.val+w.finish.val≤Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart=.ok initial)
    (startedCall : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial w.ctx w.typeIdx w.bodyStart w.finish = .ok (.Ok (),started)) :
    CompilerEntryFacts started env w.ctx w.typeIdx w.ft w.body ∧
    IndexedTableReaderCompilerPointWasm2 emit started started
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (w.ft.results.val.map Translate.valueType) (w.ctx.locals.val.map Translate.valueType)
      w.body env w.ctx.locals w.typeIdx w.ft (Wasm2.initial w.typeIdx) := by
  have all := fun more : CompilerTables => indexed_prepared_compiler_initial_wasm2
    ((CompilerTables.ofFunction started.function).append more).jumpTables
    (emit ((CompilerTables.ofFunction started.function).append more))
    ops law w bodyBound signatureTable functionTable endFits created startedCall
  exact ⟨(all .empty).1,⟨prepared_compiler_table_boundary ops law w created startedCall,fun more => (all more).2⟩⟩

end Itasca.Runtime.Code
