import Exec.Code.Body.Relations.Common.PreparedCompilerStart
import Exec.Code.Module.CompileEntryTotal
import Exec.Code.Module.CompileTotalDriver
import Itasca.Stream.ReachedBatch

namespace Exec.Code
open Aeneas Aeneas.Std Itasca
open runtime.compiler

/-- Internal remaining body obligation, restricted to independently decoded
entry metadata, captured signature tables, and the actual fresh compiler/start
calls. It does not presume a successful body or final compilation. -/
def PreparedBodiesTotal {A : Type} (ops : runtime.platform.Alloc A)
    (profile : ValidationProfile) : Prop :=
  ∀ (data : Slice U8) (env : module.Env) (index start : Usize)
    (signatures : Slice Signature) (functionSlots : Slice U32) (budget : Budget A)
    (batchStart : Usize) (initial started : FunctionCompiler A)
    (prepared : CodeEntry.Prepared data env index start profile),
    CodeEntry.Bounds env → SignatureSequence signatures.val env.types.val →
    functionSlots.val.map (fun word => word.val) = env.func_types.val.map (fun ty => signatureSlots ty.params.val) →
    batchStart.val + data.length ≤ Usize.max →
    FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial →
    FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start ops initial prepared.ctx
      prepared.typeIdx prepared.bodyStart prepared.finish = .ok (.Ok (),started) →
    CodeEntry.runBody (FunctionCompiler.Insts.ItascaCodeOpVisitor ops) profile prepared.body env
      prepared.ctx prepared.typeIdx started ⦃ _ => True ⦄

/-- All entry dispatch, local decoding, start-callback and checker obligations
are discharged; the body proof is used only at the fresh state reached here. -/
theorem compiler_entries_total_of_prepared_bodies {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (profile : ValidationProfile)
    (bodies : PreparedBodiesTotal ops profile) : ReachedEntriesTotal ops profile := by
  intro env issued scheduler worker sameEnv bounded envBounds selected held reached
  apply compiler_entry_total_of_validation ops scheduler issued worker bounded reached held.origin
  intro entry dispatched batchStart initial dispatch added created
  have reached' := StreamBatch.Reachable.dispatch reached dispatch
  obtain ⟨_,_,workerEnv,workerCode,workerOffset,workerFirst,workerCount,workerProfile⟩ := reached'.validation.1
  have envEq : dispatched.env = env := workerEnv.trans sameEnv
  have profileEq : dispatched.profile = profile := workerProfile.trans selected
  have maxRoom : limits.MAX_MODULE_BYTES.val + limits.MAX_MODULE_BYTES.val ≤ Usize.max := by
    simp only [limits.MAX_MODULE_BYTES]
    scalar_tac
  have addFits : scheduler.code_start.val + dispatched.code_offset.val ≤ Usize.max := by
    rw [workerOffset]
    have := bounded.2.2
    have := held.origin
    omega
  have arithmetic := Usize.add_spec (x := scheduler.code_start) (y := dispatched.code_offset) addFits
  rw [added,WP.spec_ok] at arithmetic
  have sourceFits : batchStart.val + dispatched.code.length ≤ Usize.max := by
    rw [workerCode]
    have bound := bounded.2.2
    have origin := held.origin
    rw [workerOffset] at arithmetic
    omega
  have range : dispatched.first_func.val + dispatched.num_funcs.val ≤ dispatched.env.func_type_indices.val.length := by
    simpa only [workerFirst,workerCount,workerEnv] using bounded.2.1
  simp only [Exec.stream.CodeBatch.validate_func]
  apply Itasca.stream.CodeBatch.validate_func.prepared_total _ dispatched entry.index initial
    (by simpa only [envEq] using envBounds) range
  · intro prepared
    exact prepared_compiler_start_total ops law prepared
      (by simpa [alloc.vec.Vec.deref,envEq] using held.signatures)
      (by have bound := prepared.body_bytes.bound; omega) created
  · intro prepared started startedCall
    have localBodies := bodies
    rw [← profileEq] at localBodies
    exact localBodies dispatched.code dispatched.env entry.index dispatched.validated_end
      (alloc.vec.Vec.deref scheduler.signatures) (alloc.vec.Vec.deref scheduler.func_param_slots)
      {scheduler.budget with marker := ()} batchStart initial started prepared
      (by simpa only [envEq] using envBounds)
      (by simpa [alloc.vec.Vec.deref,envEq] using held.signatures)
      (by simpa [alloc.vec.Vec.deref,envEq] using held.functionSlots) sourceFits created startedCall


/-- Arbitrary compiler inputs return once the reached body-loop obligation is
proved. Every other internal driver/initializer capacity fact is derived. -/
theorem compile_with_total_of_prepared_bodies {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8) (profile : ValidationProfile)
    (limits : CompileLimits) (bodies : PreparedBodiesTotal ops profile) :
    runtime.compiler.compile_with ops bytes profile limits ⦃ _ => True ⦄ :=
  compile_with_total_of_entries ops law bytes profile limits
    (compiler_entries_total_of_prepared_bodies ops law profile bodies)
end Exec.Code
