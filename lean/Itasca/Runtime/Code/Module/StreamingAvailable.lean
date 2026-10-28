import Itasca.Runtime.Code.Module.RemainingAvailable

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- The complete streaming compiler phase accepts independently certified
source regions from source-only numerical demand and allocation availability.
The certificate is produced by independent validator completeness, not by an
accepted compiler trace or a caller-supplied emitted-code certificate. -/
theorem compiler_streaming_available {A S : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (source : Itasca.stream.Source S) (state : S) (id : U64) (profile : ValidationProfile)
    (data : Slice U8) (raw : ModuleBinary.Module) (regions : Itasca.stream.SliceSource)
    (env : module.Env) (tail : module.Tail)
    (certificate : StreamCompleteRegions.Certificate data raw regions env tail profile)
    (available : StreamSource.Available source state regions.env.val regions.code.val regions.tail.val)
    (before : runtime.compiler.CompileScheduler A) (storage : module.Env) (bodyBytes localCount peak : Nat)
    (environmentDemand : EnvironmentDemand before env bound)
    (envelope : FunctionDemandEnvelope before.budget env.func_type_indices.val.length bodyBytes localCount peak bound)
    (maxima : SourcePreparationMaxima env profile bodyBytes localCount peak) (queueRoom : 4 ≤ bound)
    (emptyTypes : before.signatures.val = []) (emptySlots : before.func_param_slots.val = [])
    (emptyFunctions : before.functions.val = []) (emptyQueue : before.completed.val = [])
    (origin : before.code_start.val ≤ Itasca.limits.MAX_MODULE_BYTES.val) :
    ∃ after, ∃ run : StreamRun.Accepted source (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      id state before after env profile,
      Itasca.stream.validate_streaming source (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
        id profile state before storage = .ok (.Ok (),after,env) ∧
      run.remaining.tail = tail ∧ after.tail = some tail ∧
      CompilerQueued env before.budget bodyBytes localCount id [] env.func_type_indices.val.length after := by
  let visitor := runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops
  have hooks : ModuleTail.HooksAccept visitor.moduleModuleVisitorInst := by
    intro scheduler chunk
    exact ⟨scheduler,rfl⟩
  obtain ⟨bytes,environmentCall,environmentValue⟩ := available.environment_read
  have bytesEq : bytes = regions.env := Slice.ext _ _ environmentValue
  subst bytes
  have environmentRoom : regions.env.length ≤ Itasca.limits.MAX_MODULE_BYTES.val := by
    have length := congrArg List.length certificate.bytes
    have bound := certificate.bounded
    simp only [List.length_append,Slice.length] at length bound ⊢
    omega
  obtain ⟨environmentEnd,environmentBound,environmentLength⟩ := Itasca.limits.add_offset.complete 0#usize (Slice.len regions.env)
    (by simpa using environmentRoom)
  have endEq : environmentEnd = Slice.len regions.env := UScalar.eq_of_val_eq (by simpa using environmentLength)
  subst environmentEnd
  obtain ⟨decoded,decodeCall⟩ := module.validate_env_with.accepted_lift visitor.moduleModuleVisitorInst hooks regions.env before env
    (Slice.len regions.env) certificate.environment
  have decodedEq : decoded = before := module.validate_env_with.accepted_invariant visitor.moduleModuleVisitorInst
    (fun scheduler => scheduler = before) (compiler_custom_preserves ops _) regions.env before env (Slice.len regions.env) decoded decodeCall rfl
  subst decoded
  obtain ⟨after,remaining,tailEq,delivered,retained⟩ := compiler_remaining_available ops law bound allocation source state id profile
    data raw regions env tail certificate available before bodyBytes localCount peak environmentDemand envelope maxima queueRoom
    emptyTypes emptySlots emptyFunctions emptyQueue origin
  let run : StreamRun.Accepted source visitor id state before after env profile :=
    ⟨regions.env,Slice.len regions.env,before,before,environmentCall,environmentBound,rfl,decodeCall,remaining⟩
  exact ⟨after,run,run.run storage,tailEq,delivered,retained⟩

end Itasca.Runtime.Code
