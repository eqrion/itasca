import Exec.Code.Module.EntryFinishAvailable
import Itasca.Stream.BatchComplete

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- A valid worker entry compiles and finishes successfully, with actual worker
bookkeeping and source-paid budget charges. Only source and numerical demand
premises are supplied; no accepting visitor contract is required. -/
theorem compiler_batch_entry_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (batch : stream.CodeBatch) (index finish : Usize) (entry : ModuleBinary.Code)
    (noError : batch.error = none) (remaining : batch.num_validated.val < batch.num_funcs.val)
    (position : index.val = batch.first_func.val+batch.num_validated.val)
    (indexBound : index.val < batch.env.func_type_indices.val.length)
    (typed : Profile.EntryTyped batch.profile batch.env batch.env.func_type_indices.val[index.val] entry)
    (bounds : CodeEntry.Bounds batch.env) (environment : Profile.Environment batch.profile batch.env)
    (limits : Profile.EnvironmentWithinLimits batch.env)
    (encoded : ModuleBinary.At (Profile.CodeEncodingWithinLimits batch.profile) batch.code batch.validated_end entry finish)
    (signatures : Slice runtime.compiler.Signature) (functionSlots : Slice U32)
    (budget : runtime.compiler.Budget A) (batchStart : Usize) (initial : runtime.compiler.FunctionCompiler A)
    (signaturesMatch : SignatureSequence signatures.val batch.env.types.val)
    (slotsMatch : functionSlots.val.map (fun word => word.val) =
      batch.env.func_types.val.map (fun ty => signatureSlots ty.params.val))
    (batchBound : batchStart.val+batch.code.length ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (demand : EntryResourceDemand budget batch.code batch.env index batch.validated_end batch.profile bound) :
    ∃ count after, count.val = batch.num_validated.val+1 ∧
      stream.CodeBatch.validate_func (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        batch index initial = .ok (.Ok (),{batch with num_validated := count,validated_end := finish},after) ∧
      runtime.compiler.FunctionCompiler.finish ops after (.Ok ()) = .ok (.Ok after.function,after.budget) ∧
      ∃ w : CodeEntry.Prepared batch.code batch.env index batch.validated_end batch.profile,
        w.finish = finish ∧ CompilationBudgetEffect budget after.budget (preparedFunctionAllowance w.ctx w.body.length) := by
  obtain ⟨⟨reply,after⟩,called,accepted,ranges,header,closed,codeBound,finished,effect⟩ := WP.spec_imp_exists
    (compiler_entry_finish_available ops law bound allocation batch.code batch.env index batch.validated_end finish batch.profile
      entry indexBound typed bounds environment limits encoded signatures functionSlots budget batchStart initial
      signaturesMatch slotsMatch batchBound created demand)
  dsimp only at accepted ranges header closed codeBound finished effect
  subst reply
  obtain ⟨expected,added,expectedValue⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := batch.first_func) (y := batch.num_validated) (by scalar_tac))
  have same : expected = index := UScalar.eq_of_val_eq (by omega)
  subst expected
  have more : ¬ batch.num_validated ≥ batch.num_funcs := by scalar_tac
  have next : stream.CodeBatch.validate_next (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      batch index initial = .ok (.Ok finish,after) := by
    simp [stream.CodeBatch.validate_next,more,added,called]
  obtain ⟨count,increment,countValue⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := batch.num_validated) (y := 1#usize) (by scalar_tac))
  refine ⟨count,after,by simpa using countValue,?_,finished,effect⟩
  simp [Itasca.stream.CodeBatch.validate_func,noError,core.option.Option.is_none,next,increment]

end Itasca.Runtime.Code
