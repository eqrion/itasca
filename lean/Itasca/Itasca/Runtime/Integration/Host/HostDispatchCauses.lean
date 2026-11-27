import Itasca.Runtime.Integration.Execution.Certificates
import Itasca.Runtime.Integration.Host.HostCallContext
import Itasca.Runtime.Interp.Relations.ResourceCausesAndArgumentErrors
import Itasca.Runtime.Interp.Machine.Frames.ReturnsAndDepth

open Itasca.Representation

/-!
# Host dispatch resource causes

Selected source host calls fix source signatures and shared argument bases, including suspended callers. Cause relations retain concrete allocation, interrupt and callback failures.
-/

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Interp

/-- A selected source host call fixes both its source signature and its shared
argument base, including suspended source callers. -/
def HostSignatureSite (source : SourceMachine.AState) (address : funcaddr) (identity : Nat)
    (signature : Itasca.wasm_types.FuncType) (base : Nat) : Prop :=
  SourceInvocationSite source address base ∧ HostFunction source.store address identity
    (signature.params.val.map Itasca.Translation.valueType) (signature.results.val.map Itasca.Translation.valueType)

/-- The actual dispatch calls the selected host with an exact PC-updated
execution. Every refusal is the retained concrete helper's own cause. -/
def HostDispatchCause {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (source : SourceMachine.AState)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P)
    (error : runtime.ExecError) : Prop :=
  out.1=.Err error ∧ ∃ (index : Usize) (raw : runtime.interp.Frame) (pc : U32)
    (address : runtime.FuncAddr) (signature : Itasca.wasm_types.FuncType) (base : Usize) (identity : U64),
    exec.frames.val[index.val]?=some raw ∧ pc.val=raw.pc.val+1 ∧
    HostSignatureSite source address.index.val identity.val signature base.val ∧
    runtime.interp.call memory hooks floats allocator {exec with frames:=exec.frames.set index {raw with pc:=pc}}
      store platform address base=.ok out ∧
    HostCallCauses allocator hooks {exec with frames:=exec.frames.set index {raw with pc:=pc}}
      store platform signature base identity out

theorem HostSignatureSite.prepend {before middle : SourceMachine.AState} {address identity signature base}
    (site : HostSignatureSite middle address identity signature base)
    (steps : StepsH (SourceMachine.decode before) [] (SourceMachine.decode middle))
    (sameStore : middle.store=before.store) (sameAmbient : middle.ambient=before.ambient) :
    HostSignatureSite before address identity signature base := by
  obtain ⟨count,trace⟩ := Spec.steps_h_count steps
  refine ⟨?_,by simpa only [sameStore] using site.2⟩
  rcases site.1 with direct | indirect
  · exact Or.inl (direct.prepend trace sameStore sameAmbient)
  · exact Or.inr (indirect.prepend trace sameStore sameAmbient)

theorem HostDispatchCause.prepend {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    {before middle : SourceMachine.AState} {out error}
    (cause : HostDispatchCause memory hooks floats allocator exec store platform middle out error)
    (steps : StepsH (SourceMachine.decode before) [] (SourceMachine.decode middle))
    (sameStore : middle.store=before.store) (sameAmbient : middle.ambient=before.ambient) :
    HostDispatchCause memory hooks floats allocator exec store platform before out error := by
  obtain ⟨failed,index,raw,pc,address,signature,base,identity,found,next,site,actual,refused⟩ := cause
  exact ⟨failed,index,raw,pc,address,signature,base,identity,found,next,
    site.prepend steps sameStore sameAmbient,actual,refused⟩

theorem HostDispatchCause.source_values {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    {source : SourceMachine.AState} {out}
    (cause : HostDispatchCause memory hooks floats allocator exec store platform source out (.Exhausted .Values)) :
    ∃ address identity base params results, SourceInvocationSite source address base ∧
      HostFunction source.store address identity params results ∧
      store.limits.max_values.val<base+max (Representation.slots params) (Representation.slots results) := by
  obtain ⟨failed,index,raw,pc,address,signature,base,identity,found,next,site,actual,refused⟩ := cause
  simp only [HostCallCauses,failed,HostPreparationCause,hostSlotDemand,typeSlots] at refused
  exact ⟨address.index.val,identity.val,base.val,_,_,site.1,site.2,by simpa only [Nat.max_comm] using refused⟩

theorem HostDispatchCause.source_allocation {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    {source : SourceMachine.AState} {out}
    (cause : HostDispatchCause memory hooks floats allocator exec store platform source out (.Exhausted .Allocation)) :
    ∃ address identity base params results, SourceInvocationSite source address base ∧
      HostFunction source.store address identity params results ∧ HostSignatureAllocation allocator params results base := by
  obtain ⟨failed,index,raw,pc,address,signature,base,identity,found,next,site,actual,refused⟩ := cause
  simp only [HostCallCauses,failed,HostPreparationCause] at refused
  refine ⟨address.index.val,identity.val,base.val,_,_,site.1,site.2,?_⟩
  rcases refused with ⟨n,bound,allocation⟩ | ⟨n,bound,allocation⟩ | ⟨n,bound,allocation⟩
  · exact Or.inl ⟨exec.slots,n,by simpa only [hostSlotDemand,typeSlots,Nat.max_comm] using bound,allocation⟩
  · exact Or.inr (Or.inl ⟨exec.host_args,n,by simpa only [List.length_map] using bound,allocation⟩)
  · exact Or.inr (Or.inr ⟨exec.host_results,n,by simpa only [List.length_map] using bound,allocation⟩)

theorem HostDispatchCause.interrupted {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    {source : SourceMachine.AState} {out}
    (cause : HostDispatchCause memory hooks floats allocator exec store platform source out .Terminated) :
    ∃ after, hooks.interrupt platform=.ok (.Terminate,after) := by
  obtain ⟨failed,index,raw,pc,address,signature,base,identity,found,next,site,actual,refused⟩ := cause
  simpa only [HostCallCauses,failed,HostPreparationCause] using refused

theorem HostDispatchCause.host_overflow {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    {source : SourceMachine.AState} {out}
    (cause : HostDispatchCause memory hooks floats allocator exec store platform source out (.Exhausted .CallStack)) :
    ∃ identity p args defaults returned,
      hooks.call_host p store identity args defaults=.ok (.Err .StackOverflow,out.2.2.2,out.2.2.1,returned) := by
  obtain ⟨failed,index,raw,pc,address,signature,base,identity,found,next,site,actual,refused⟩ := cause
  exact ⟨identity,by simpa only [HostCallCauses,failed] using refused⟩
end Itasca.Integration
