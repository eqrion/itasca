import Itasca.Runtime.Compiler.Body.Relations.Table.PreparedTableInitial
import Itasca.Runtime.Compiler.Body.Relations.Entry.PreparedRawInitial
import Itasca.Runtime.Compiler.Module.CompileProfileTotal
import Itasca.Runtime.Compiler.Body.Relations.Executable.ExecutableEmission
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Actual entry setup supplies every static and allocation ledger field needed
by the reached-body normality proof, before reading any instruction. -/
theorem prepared_executable_safety_wasm2 {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial started : runtime.compiler.FunctionCompiler A} {data env index start profile}
    (w : CodeEntry.Prepared data env index start profile)
    (small : w.body.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (signaturesMatch : SignatureSequence signatures.val env.types.val)
    (slotsMatch : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ty => signatureSlots ty.params.val))
    (batchBound : batchStart.val + data.length ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (begun : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial w.ctx w.typeIdx w.bodyStart w.finish = .ok (.Ok (),started)) :
    let C := EnvTranslation.context env w.ctx
    CompilerEntryFacts started env w.ctx w.typeIdx w.ft w.body ∧
    EnvTranslation.Matches env ⟨w.ctx.locals,w.ft.results⟩ C ∧
    IndexedTableReaderCompilerPointWasm2 (fun tables => ExecutableEmission tables C) started started
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (w.ft.results.val.map Translate.valueType) (w.ctx.locals.val.map Translate.valueType)
      w.body env w.ctx.locals w.typeIdx w.ft (Wasm2.initial w.typeIdx) ∧
    ObservedStack started [] ∧
    started.function.indirect.val.length ≤ started.function.code.val.length ∧
    started.function.simd.val.length ≤ started.function.code.val.length ∧
    started.function.v128_pool.val.length ≤ started.function.code.val.length ∧
    FixupBudget started.frames.val started.function.code.val.length := by
  have endFits : batchStart.val + w.finish.val ≤ Usize.max := by
    have bound := w.body_bytes.bound
    omega
  obtain ⟨facts,point⟩ := indexed_table_prepared_compiler_initial_wasm2
    (fun tables => ExecutableEmission tables (EnvTranslation.context env w.ctx))
    ops law w small signaturesMatch slotsMatch endFits created begun
  refine ⟨facts,?_,point,prepared_compiler_raw_initial ops law w signaturesMatch endFits created begun⟩
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  simp only [EnvTranslation.context,w.context_results]

end Itasca.Runtime.Code
