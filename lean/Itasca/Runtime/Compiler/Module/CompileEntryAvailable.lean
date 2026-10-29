import Itasca.Runtime.Compiler.Module.EntryFinishAvailable
import Itasca.Stream.BatchComplete
import Itasca.Runtime.Compiler.Module.CompileEntry

/-!
Successful scheduled entry compilation from batch entry availability.
-/

/-! ## Batch Entry Available -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## Compile Entry Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The scheduler compiles and publishes an independently valid dispatched
entry into its vacant source-indexed slot. All compiler calls, including finish,
are constructed from source-only demand and bounded allocation availability. -/
theorem compiler_scheduled_entry_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.CompileScheduler A) (batch dispatched : stream.CodeBatch)
    (frame : stream.CodeEntry) (finish : Usize) (entry : ModuleBinary.Code)
    (dispatch : stream.CodeBatch.next_entry batch = .ok (.Ok frame,dispatched))
    (noError : dispatched.error = none) (remaining : dispatched.num_validated.val < dispatched.num_funcs.val)
    (position : frame.index.val = dispatched.first_func.val+dispatched.num_validated.val)
    (indexBound : frame.index.val < dispatched.env.func_type_indices.val.length)
    (typed : Profile.EntryTyped dispatched.profile dispatched.env dispatched.env.func_type_indices.val[frame.index.val] entry)
    (bounds : CodeEntry.Bounds dispatched.env) (environment : Profile.Environment dispatched.profile dispatched.env)
    (limits : Profile.EnvironmentWithinLimits dispatched.env)
    (encoded : ModuleBinary.At (Profile.CodeEncodingWithinLimits dispatched.profile)
      dispatched.code dispatched.validated_end entry finish)
    (signaturesMatch : SignatureSequence before.signatures.val dispatched.env.types.val)
    (slotsMatch : before.func_param_slots.val.map (fun word => word.val) =
      dispatched.env.func_types.val.map (fun ty => signatureSlots ty.params.val))
    (batchBound : before.code_start.val+dispatched.code_offset.val+dispatched.code.length ≤ Usize.max)
    (slotBound : frame.index.val < before.functions.val.length)
    (vacant : before.functions.val[frame.index.val]? = some none)
    (demand : EntryResourceDemand (A := A) {before.budget with marker := ()} dispatched.code dispatched.env
      frame.index dispatched.validated_end dispatched.profile bound) :
    ∃ (count : Usize) (final : runtime.compiler.FunctionCompiler A),
      count.val = dispatched.num_validated.val+1 ∧
      runtime.compiler.CompileScheduler.compile_entry ops before batch = .ok (.Ok (),
        {before with functions := before.functions.set frame.index (some final.function),budget := final.budget},
        {dispatched with num_validated := count,validated_end := finish}) ∧
      ∃ w : CodeEntry.Prepared dispatched.code dispatched.env frame.index dispatched.validated_end dispatched.profile,
        w.finish = finish ∧ CompilationBudgetEffect before.budget final.budget (preparedFunctionAllowance w.ctx w.body.length) := by
  obtain ⟨batchStart,added,startValue⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := before.code_start) (y := dispatched.code_offset) (by omega))
  obtain ⟨initial,created,_⟩ := WP.spec_imp_exists (compiler_new ops
    (alloc.vec.Vec.deref before.signatures) (alloc.vec.Vec.deref before.func_param_slots)
    {before.budget with marker := ()} batchStart)
  obtain ⟨count,final,countValue,validated,finished,w,ending,effect⟩ := compiler_batch_entry_available ops law bound allocation
    dispatched frame.index finish entry noError remaining position indexBound typed bounds environment limits encoded
    (alloc.vec.Vec.deref before.signatures) (alloc.vec.Vec.deref before.func_param_slots)
    {before.budget with marker := ()} batchStart initial (by simpa [alloc.vec.Vec.deref] using signaturesMatch)
    (by simpa [alloc.vec.Vec.deref] using slotsMatch) (by omega) created demand
  let finalBatch := {dispatched with num_validated := count,validated_end := finish}
  let after := {before with functions := before.functions.set frame.index (some final.function),budget := final.budget}
  refine ⟨count,final,countValue,?_,w,ending,?_⟩
  · unfold runtime.compiler.CompileScheduler.compile_entry
    simp only [dispatch,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,
      runtime.compiler.Budget.copy_state,Itasca.stream.CodeBatch.impl.code_offset,
      uncurry_apply_pair,added,created,validated,finished]
    have fits : ¬ frame.index ≥ alloc.vec.Vec.len before.functions := by scalar_tac
    simp only [fits,↓reduceIte]
    have found := alloc.vec.Vec.index_usize_spec before.functions frame.index slotBound
    have missing : before.functions.val[frame.index.val] = none := by
      simpa only [List.getElem?_eq_getElem slotBound,Option.some.injEq] using vacant
    simp only [missing] at found
    obtain ⟨existing,lookup,same⟩ := WP.spec_imp_exists found
    subst existing
    simp only [alloc.vec.Vec.index_slice_index]
    rw [lookup]
    simp only [bind_ok,core.option.Option.is_some,↓reduceIte]
    obtain ⟨⟨old,back⟩,mutable,oldEq,backEq⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.index_mut_usize_spec before.functions frame.index slotBound)
    simp only [alloc.vec.Vec.index_mut_slice_index]
    rw [mutable]
    simp only [bind_ok,uncurry_apply_pair,backEq]
    rfl
  · simpa only [CompilationBudgetEffect] using effect

end Itasca.Runtime.Compiler

end
