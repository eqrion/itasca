import Exec.Code.Module.PreparedBatchSource
import Exec.Code.Module.DispatchEntryAvailable
import Exec.Code.Module.CompileEntryAvailable
import Exec.Code.Module.FunctionSlotPrefix
import Exec.Code.Module.CompileEntries

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private theorem increment_room (index count : Usize) (remaining : index.val < count.val) :
    index.val+1 ≤ Usize.max := by scalar_tac

/-- The actual eager batch loop accepts an independent prepared source sequence.
The uniform numerical envelope pays cumulative charges across all functions;
publication fills each source slot once, including unreachable body code. -/
theorem compiler_batch_loop_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (base : runtime.compiler.Budget A) (bodyBytes localCount peak : Nat)
    (before : runtime.compiler.CompileScheduler A) (batch : stream.CodeBatch)
    (loopIndex finish : Usize) (entries : List ModuleBinary.Code)
    (source : PreparedBatchSource batch.code batch.env batch.profile bodyBytes localCount peak
      (batch.first_func.val+batch.num_validated.val) batch.validated_end entries finish)
    (envelope : FunctionDemandEnvelope base batch.env.func_type_indices.val.length bodyBytes localCount peak bound)
    (paid : CompilationBudgetEffect base before.budget
      (fun counter => (batch.first_func.val+batch.num_validated.val)*functionDemandRate bodyBytes localCount counter))
    (slots : FunctionSlotPrefix batch.env.func_type_indices.val.length
      (batch.first_func.val+batch.num_validated.val) before.functions.val)
    (synchronized : batch.num_dispatched = batch.num_validated) (cursor : batch.dispatch_end = batch.validated_end)
    (noError : batch.error = none) (iteration : loopIndex = batch.num_validated)
    (count : batch.num_validated.val+entries.length = batch.num_funcs.val)
    (range : batch.first_func.val+batch.num_funcs.val ≤ batch.env.func_type_indices.val.length)
    (bounds : CodeEntry.Bounds batch.env) (environment : Profile.Environment batch.profile batch.env)
    (limits : Profile.EnvironmentWithinLimits batch.env)
    (signatures : SignatureSequence before.signatures.val batch.env.types.val)
    (functionSlots : before.func_param_slots.val.map (fun word => word.val) =
      batch.env.func_types.val.map (fun ty => signatureSlots ty.params.val))
    (coordinates : batch.code_offset.val+batch.code.length ≤ Itasca.limits.MAX_MODULE_BYTES.val)
    (arithmetic : before.code_start.val+batch.code_offset.val+batch.code.length ≤ Usize.max) :
    ∃ after worker,
      runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop ops before batch loopIndex (.Ok ()) =
        .ok (submitPack after worker (.Ok ())) ∧
      worker.num_validated = batch.num_funcs ∧ worker.validated_end = finish ∧ worker.error = none ∧
      after.completed = before.completed ∧
      FunctionSlotPrefix batch.env.func_type_indices.val.length (batch.first_func.val+batch.num_funcs.val) after.functions.val ∧
      CompilationBudgetEffect base after.budget
        (fun counter => (batch.first_func.val+batch.num_funcs.val)*functionDemandRate bodyBytes localCount counter) := by
  induction entries generalizing before batch loopIndex with
  | nil =>
    cases source
    have ended : batch.num_validated = batch.num_funcs := UScalar.eq_of_val_eq (by simpa using count)
    subst loopIndex
    refine ⟨before,batch,?_,ended,rfl,noError,rfl,?_,?_⟩
    · rw [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop,loop]
      simp [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop.body,
        Exec.stream.CodeBatch.len,Itasca.stream.CodeBatch.len,ended,submitPack]
    · simpa only [ended] using slots
    · simpa only [ended] using paid
  | cons entry entries ih =>
    cases source with
    | cons ordinal ordinalValue indexBound typed encoded prepared ending bytes locals operands rest =>
      have more : batch.num_validated.val < batch.num_funcs.val := by simp only [List.length_cons] at count; omega
      obtain ⟨raw,encoding,span⟩ := encoded
      have encoded : ModuleBinary.At (Profile.CodeEncodingWithinLimits batch.profile) batch.code batch.validated_end entry prepared.finish :=
        ending ▸ ⟨raw,encoding,span⟩
      have rawEncoded : ModuleBinary.At (Profile.CodeEncoding batch.profile) batch.code batch.validated_end entry prepared.finish :=
        ⟨raw,encoding.encoding,by simpa only [ending] using span⟩
      obtain ⟨content,extent⟩ := rawEncoded.code_extent
      obtain ⟨index,dispatchedCount,frame,indexValue,dispatchedValue,frameIndex,dispatch⟩ :=
        compiler_next_entry_available batch content prepared.finish (by simpa only [synchronized] using more)
          (range.trans batch.env.func_type_indices.property) (by simpa only [cursor] using extent)
          (by have endBound := rawEncoded.span.2; omega)
      rw [synchronized] at indexValue dispatchedValue
      have selected : frame.index = ordinal := UScalar.eq_of_val_eq (by rw [frameIndex]; omega)
      cases selected
      let dispatched := {batch with num_dispatched := dispatchedCount,dispatch_end := prepared.finish}
      have localDemand : EntryResourceDemand (A := A) {before.budget with marker := ()} batch.code batch.env
          frame.index batch.validated_end batch.profile bound := by
        apply EntryResourceDemand.of_prepared prepared
        exact envelope.prepared (by simpa only [CompilationBudgetEffect] using paid) (by omega)
          prepared.ctx prepared.body.length _ bytes locals operands
      obtain ⟨validatedCount,final,validatedValue,compiled,w,finished,effect⟩ := compiler_scheduled_entry_available ops law bound allocation
        before batch dispatched frame prepared.finish entry dispatch noError more ordinalValue
        indexBound typed bounds environment limits
        encoded signatures functionSlots arithmetic
        (by rw [slots.length]; exact indexBound)
        (by rw [ordinalValue]; exact slots.vacant _ (Nat.le_refl _) (by omega))
        localDemand
      dsimp only [dispatched] at validatedValue
      have unique := prepared_entry_unique prepared w
      have allowance : ∀ counter, preparedFunctionAllowance w.ctx w.body.length counter ≤ functionDemandRate bodyBytes localCount counter := by
        obtain ⟨_,sameCtx,sameBody,_,_⟩ := unique
        exact prepared_allowance_le_rate _ _ _ _ (by simpa only [←sameBody] using bytes) (by simpa only [←sameCtx] using locals)
      let nextScheduler := {before with functions := before.functions.set frame.index (some final.function),budget := final.budget}
      let nextBatch := {dispatched with num_validated := validatedCount,validated_end := prepared.finish}
      have nextPaid : CompilationBudgetEffect base nextScheduler.budget
          (fun counter => (nextBatch.first_func.val+nextBatch.num_validated.val)*functionDemandRate bodyBytes localCount counter) := by
        have combined := paid.trans (effect.weaken allowance)
        apply combined.weaken
        intro counter
        dsimp only [nextBatch,dispatched]
        rw [validatedValue]
        simp only [Nat.add_mul,Nat.one_mul]
        omega
      have nextSlots : FunctionSlotPrefix nextBatch.env.func_type_indices.val.length
          (nextBatch.first_func.val+nextBatch.num_validated.val) nextScheduler.functions.val := by
        have published := slots.publish (by omega) final.function
        simpa only [nextBatch,dispatched,nextScheduler,alloc.vec.Vec.set_val_eq,ordinalValue,validatedValue,Nat.add_assoc] using published
      have restSource : PreparedBatchSource nextBatch.code nextBatch.env nextBatch.profile bodyBytes localCount peak
          (nextBatch.first_func.val+nextBatch.num_validated.val) nextBatch.validated_end entries finish := by
        simpa only [nextBatch,dispatched,validatedValue,Nat.add_assoc,ending] using rest
      obtain ⟨after,worker,continued,validated,ended,error,queue,published,charged⟩ := ih nextScheduler nextBatch validatedCount restSource
        envelope nextPaid nextSlots (by apply UScalar.eq_of_val_eq; dsimp only [nextBatch,dispatched]; rw [dispatchedValue,validatedValue]) rfl
        noError rfl (by dsimp only [nextBatch,dispatched]; simp only [List.length_cons] at count; omega)
        range bounds environment limits signatures functionSlots coordinates arithmetic
      refine ⟨after,worker,?_,validated,ended,error,queue,published,charged⟩
      subst loopIndex
      obtain ⟨incremented,increment,incrementValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := batch.num_validated) (y := 1#usize) (by simpa using increment_room _ _ more))
      have incrementEq : incremented = validatedCount := UScalar.eq_of_val_eq (by simpa only [show (1#usize).val = 1 from rfl] using incrementValue.trans validatedValue.symm)
      subst incremented
      rw [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop,loop]
      simp only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop.body,
        Exec.stream.CodeBatch.len,Itasca.stream.CodeBatch.len,bind_ok]
      have live : batch.num_validated < batch.num_funcs := by simpa only [UScalar.lt_equiv] using more
      simp only [live,↓reduceIte,core.result.Result.is_ok,bind_ok,compiled,uncurry_apply_pair,increment]
      simpa only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop,
        runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop.body,
        Exec.stream.CodeBatch.len,Itasca.stream.CodeBatch.len,bind_ok,core.result.Result.is_ok] using continued

end Exec.Code
