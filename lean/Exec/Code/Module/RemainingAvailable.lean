import Exec.Code.Module.EnvironmentCompilationAvailable
import Exec.Code.Module.SourceSubmissionAvailable
import Exec.Code.Module.CompileDriverFrame
import Itasca.Stream.DriverComplete

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

private theorem compiler_hooks_accept {A : Type} (ops : runtime.platform.Alloc A) :
    ModuleTail.HooksAccept (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops).moduleModuleVisitorInst := by
  intro before chunk
  exact ⟨before,rfl⟩

/-- Actual environment capture, all issued batches, tail delivery, and final
reverse-order retirement accept from independent region validity and numerical
demand. No successful compiler call or emitted certificate is an input. -/
theorem compiler_remaining_available {A S : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (source : Itasca.stream.Source S) (state : S) (id : U64) (profile : ValidationProfile)
    (data : Slice U8) (raw : ModuleBinary.Module) (regions : Itasca.stream.SliceSource)
    (env : module.Env) (tail : module.Tail)
    (certificate : StreamCompleteRegions.Certificate data raw regions env tail profile)
    (available : StreamSource.Available source state regions.env.val regions.code.val regions.tail.val)
    (before : runtime.compiler.CompileScheduler A) (bodyBytes localCount peak : Nat)
    (environmentDemand : EnvironmentDemand before env bound)
    (envelope : FunctionDemandEnvelope before.budget env.func_type_indices.val.length bodyBytes localCount peak bound)
    (maxima : SourcePreparationMaxima env profile bodyBytes localCount peak) (queueRoom : 4 ≤ bound)
    (emptyTypes : before.signatures.val = []) (emptySlots : before.func_param_slots.val = [])
    (emptyFunctions : before.functions.val = []) (emptyQueue : before.completed.val = [])
    (origin : before.code_start.val ≤ Itasca.limits.MAX_MODULE_BYTES.val) :
    ∃ after, ∃ run : StreamRun.Remaining source (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      id state env (Slice.len regions.env) before after profile,
      run.tail = tail ∧ after.tail = some tail ∧
      CompilerQueued env before.budget bodyBytes localCount id [] env.func_type_indices.val.length after := by
  let visitor := runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops
  let Queued := CompilerQueued env before.budget bodyBytes localCount
  have policy := compiler_queue_policy ops law bound allocation env profile before.budget bodyBytes localCount peak envelope maxima queueRoom
  obtain ⟨len,lengthCall,lengthValue⟩ := available.code_len_read
  have lengthEq : len = Slice.len regions.code := UScalar.eq_of_val_eq lengthValue
  subst len
  have codeRoom : regions.env.length+regions.code.length ≤ Itasca.limits.MAX_MODULE_BYTES.val := by
    have bytes := congrArg List.length certificate.bytes
    have bounded := certificate.bounded
    simp only [List.length_append,Slice.length] at bytes bounded ⊢
    omega
  obtain ⟨codeEnd,codeBound,codeEndValue⟩ := Itasca.limits.add_offset.complete
    (Slice.len regions.env) (Slice.len regions.code) (by simpa using codeRoom)
  obtain ⟨entries,header,encoded⟩ := certificate.code
  have headerCall := Itasca.stream.read_code_header.complete source state (Slice.len regions.code)
    env entries regions.code regions.env.val regions.tail.val available rfl (by omega) header
  obtain ⟨⟨reply,configured⟩,configuredCall,status,configuredReady,configuredTail⟩ := WP.spec_imp_exists
    (compiler_environment_compilation_available ops law bound allocation before env bodyBytes localCount environmentDemand
      emptyTypes emptySlots emptyFunctions emptyQueue origin)
  dsimp only at status configuredReady configuredTail
  subst reply
  obtain ⟨pending,submitted,queue,submitCall,submittedReady,valid,ids,pendingBound⟩ := StreamAvailability.submit_complete source visitor Queued
    ⟨25000#usize,4#usize⟩ state id env regions.code policy entries regions.env.val regions.tail.val available
    certificate.entry_bounds certificate.profile certificate.signature_limits (by omega) raw.codes certificate.code_count certificate.typed encoded
    configured configuredReady
  obtain ⟨tailBytes,tailCall,tailValue⟩ := available.tail_read
  have tailEq : tailBytes = regions.tail := Slice.ext _ _ tailValue
  subst tailBytes
  have wholeRoom : codeEnd.val+regions.tail.length ≤ Itasca.limits.MAX_MODULE_BYTES.val := by
    have endEq : codeEnd.val = regions.env.length+regions.code.length := by simpa using codeEndValue
    have bytesLength : data.length = regions.env.length+regions.code.length+regions.tail.length := by
      simpa [List.length_append,Nat.add_assoc] using congrArg List.length certificate.bytes
    rw [endEq,←bytesLength]
    exact certificate.bounded
  obtain ⟨moduleEnd,moduleBound,_⟩ := Itasca.limits.add_offset.complete codeEnd (Slice.len regions.tail) (by simpa using wholeRoom)
  obtain ⟨decoded,decodedCall⟩ := module.validate_tail_with.accepted_lift visitor.moduleModuleVisitorInst
    (compiler_hooks_accept ops) regions.tail 0#usize env submitted tail certificate.tail_accepted
  have decodedEq : decoded = submitted := module.validate_tail_with.accepted_invariant visitor.moduleModuleVisitorInst
    (fun scheduler => scheduler = submitted) (compiler_custom_preserves ops _) regions.tail 0#usize env submitted tail decoded decodedCall rfl
  subst decoded
  let ready := {submitted with tail := some tail}
  have readyQueued : Queued id queue env.func_type_indices.val.length ready := by
    obtain ⟨stateReady,workers⟩ := submittedReady
    exact ⟨⟨stateReady.signatures,stateReady.functionSlots,stateReady.origin,stateReady.slots,stateReady.paid⟩,workers⟩
  obtain ⟨after,remaining,drainCall,empty,afterQueued⟩ := StreamAvailability.drain_complete visitor ⟨25000#usize,4#usize⟩ env profile Queued policy
    id queue env.func_type_indices.val.length ready pending readyQueued valid ids
  have finalFrame := compiler_drain_frame ops id ready after pending remaining drainCall
  refine ⟨after,⟨Slice.len regions.code,codeEnd,entries,⟨25000#usize,4#usize⟩,configured,pending,submitted,submitted,
    regions.tail,moduleEnd,submitted,tail,submitted,ready,remaining,lengthCall,codeBound,headerCall,configuredCall,
    by decide,by decide,submitCall,rfl,tailCall,moduleBound,rfl,decodedCall,rfl,drainCall⟩,rfl,?_,afterQueued⟩
  rw [finalFrame]

end Itasca.Runtime.Code
