import Exec.Code.Module.BatchEntryAvailable
import Exec.Code.Module.CompileEntry

namespace Exec.Code
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
    (limits : Profile.EnvironmentWithinLimits dispatched.profile dispatched.env)
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
  have dispatchedCall := dispatch
  simp only [Exec.stream.CodeBatch.next_entry] at dispatchedCall
  have validatedCall := validated
  simp only [Exec.stream.CodeBatch.validate_func] at validatedCall
  let finalBatch := {dispatched with num_validated := count,validated_end := finish}
  let after := {before with functions := before.functions.set frame.index (some final.function),budget := final.budget}
  refine ⟨count,final,countValue,?_,w,ending,?_⟩
  · unfold runtime.compiler.CompileScheduler.compile_entry
    simp only [Exec.stream.CodeBatch.next_entry,dispatchedCall,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,
      runtime.compiler.Budget.copy_state,Exec.stream.CodeBatch.code_offset,Itasca.stream.CodeBatch.impl.code_offset,
      uncurry_apply_pair,added,created,Exec.stream.CodeBatch.validate_func,validatedCall,finished]
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

end Exec.Code
