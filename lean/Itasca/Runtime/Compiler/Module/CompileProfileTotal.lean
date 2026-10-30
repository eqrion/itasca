import Itasca.Runtime.Compiler.Module.CompileTotalDriver
import Itasca.Runtime.Compiler.Body.Relations.Entry.PreparedCompilerStart
import Itasca.Runtime.Compiler.Module.CompileEntryTotal
import Itasca.Runtime.Compiler.Module.SchedulerProfileSafety
import Itasca.Stream.ReachedBatch

/-!
Normal return of default and explicit-profile compilation, projecting the shared generic compiler totality proof.
-/

/-! ## Compile Default Total -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
open runtime.compiler

@[step] theorem compiler_default_limits_total :
    CompileLimits.Insts.CoreDefaultDefault.default ⦃ _ => True ⦄ := by
  unfold CompileLimits.Insts.CoreDefaultDefault.default
  step
  step

end Itasca.Runtime.Compiler

end

/-! ## Compile Profile Total -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
open runtime.compiler

/-- Internal remaining body obligation, restricted to independently decoded
entry metadata, captured signature tables, and the actual fresh compiler/start
calls. It does not presume a successful body or final compilation. -/
def ProfilePreparedBodiesTotal {A : Type} (ops : runtime.platform.Alloc A)
    (profile : ValidationProfile) : Prop :=
  ∀ (data : Slice U8) (env : metadata.Env) (index start : Usize)
    (signatures : Slice Signature) (functionSlots : Slice U32) (budget : Budget A)
    (batchStart : Usize) (initial started : FunctionCompiler A)
    (prepared : CodeEntry.Prepared data env index start profile),
    CodeEntry.Bounds env → ProfileEnvironment profile env → SignatureSequence signatures.val env.types.val →
    functionSlots.val.map (fun word => word.val) = env.func_types.val.map (fun ty => signatureSlots ty.params.val) →
    batchStart.val + data.length ≤ Usize.max →
    FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial →
    FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start ops initial prepared.ctx
      prepared.typeIdx prepared.bodyStart prepared.finish = .ok (.Ok (),started) →
    code.validate_body_with (FunctionCompiler.Insts.ItascaCodeOpVisitor ops) prepared.body env prepared.ctx
      prepared.typeIdx profile started ⦃ _ => True ⦄

/-- All entry dispatch, local decoding, start-callback and checker obligations
are discharged; the body proof is used only at the fresh state reached here. -/
theorem compiler_profile_entries_total_of_prepared_bodies {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (profile : ValidationProfile)
    (bodies : ProfilePreparedBodiesTotal ops profile) : ReachedProfileEntriesTotal ops profile := by
  intro env issued scheduler worker sameEnv bounded envBounds selected admitted held reached
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
      (by simpa only [envEq,profileEq] using admitted)
      (by simpa [alloc.vec.Vec.deref,envEq] using held.signatures)
      (by simpa [alloc.vec.Vec.deref,envEq] using held.functionSlots) sourceFits created startedCall


/-- Driver normality with the profile constraints supplied by actual environment
validation. No restriction on the input bytes is required. -/
theorem compile_with_total_of_profile_entries {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8) (profile : ValidationProfile)
    (limits : CompileLimits) (entries : ReachedProfileEntriesTotal ops profile) :
    runtime.compiler.compile_with ops bytes profile limits ⦃ _ => True ⦄ := by
  apply compile_with_total_of_streaming ops law bytes profile limits
  intro codeStart codeEnd storage bounds
  by_cases small : codeStart.val ≤ Itasca.limits.MAX_MODULE_BYTES.val
  · exact compiler_stream_spec_of_profile_entries ops law profile entries
      {bytes,code_start := codeStart,code_end := codeEnd} bounds _
      ⟨rfl,rfl,rfl,rfl,small⟩ storage
  · rw [compiler_stream_large_environment _ profile
      {bytes,code_start := codeStart,code_end := codeEnd} bounds
      (by change Itasca.limits.MAX_MODULE_BYTES.val < codeStart.val; omega)]
    simp

/-- The complete driver reduces to body normality at profile-valid, actually
prepared function entries. Header, local, initializer and checker paths are derived. -/
theorem compile_with_total_of_profile_prepared_bodies {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8) (profile : ValidationProfile)
    (limits : CompileLimits) (bodies : ProfilePreparedBodiesTotal ops profile) :
    runtime.compiler.compile_with ops bytes profile limits ⦃ _ => True ⦄ :=
  compile_with_total_of_profile_entries ops law bytes profile limits
    (compiler_profile_entries_total_of_prepared_bodies ops law profile bodies)
end Itasca.Runtime.Compiler

end
