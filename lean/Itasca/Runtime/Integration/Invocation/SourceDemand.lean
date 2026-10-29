import Itasca.Runtime.Integration.Invocation.DefinedResources
import Itasca.Runtime.Integration.Invocation.InitialHostCauses
import Itasca.Runtime.Integration.Api.InitialHostResourcesAdequate
import Itasca.Runtime.Integration.Api.InvocationResourcesAdequate

/-! Source-level resource demand of an invocation, and how it rules out every resource cause
of a public invocation error. -/
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec Itasca.Runtime.Interp

/-- Source storage demand at a selected point, including defined and host
callees and suspended callers. No native success or trace appears here. -/
structure SourceWorldResources (valueLimit frameLimit : Nat) (source : SourceMachine.AState) : Prop where
  frames : frameDepth (SourceMachine.decode source)<frameLimit
  defined : ∀ address base words,SourceInvocationSite source address base →
    SourceCanonicalFunctionCapacity source.store address words → base+words≤valueLimit
  host : ∀ address identity base params results,SourceInvocationSite source address base →
    HostFunction source.store address identity params results → base+max (Compiler.slots params) (Compiler.slots results)≤valueLimit

theorem EventfulSourceResourceCause.excludes_boundary {M P A : Type} {hooks : runtime.platform.Platform P M}
    {allocator : runtime.platform.Alloc A} {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {machine : EventfulMachine M P view code expected} {out : EventfulDispatchResult M P} {error : runtime.ExecError}
    {valueLimit frameLimit : Nat}
    (resources : SourceWorldResources valueLimit frameLimit machine.source)
    (valueFloor : valueLimit≤machine.store.limits.max_values.val) (frameFloor : frameLimit≤machine.store.limits.max_frames.val)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after))
    (overflow : ∀ p identity args defaults nextPlatform after returned,
      hooks.call_host p machine.store identity args defaults≠.ok (.Err .StackOverflow,nextPlatform,after,returned))
    (cause : EventfulSourceResourceCause hooks allocator machine out error)
    (kind : error=.Terminated ∨ error=.Exhausted .CallStack ∨ error=.Exhausted .Values ∨ error=.Exhausted .Allocation ∨ error=.Exhausted .Objects) : False := by
  rcases kind with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨after,refused⟩ := cause
    exact continuing _ _ refused
  · rcases cause with depth | ⟨identity,p,args,defaults,returned,refused⟩
    · have bounded := resources.frames
      omega
    · exact overflow p identity args defaults _ _ returned refused
  · obtain ⟨address,base,site,defined | host⟩ := cause
    · obtain ⟨words,capacity,exceeds⟩ := defined
      have bounded := resources.defined address base words site capacity
      omega
    · obtain ⟨identity,params,results,signature,exceeds⟩ := host
      have bounded := resources.host address identity base params results site signature
      omega
  · rcases cause with ⟨address,base,words,site,capacity,refusal⟩ | ⟨address,identity,base,params,results,site,signature,refusal⟩
    · rcases refusal with ⟨slots,n,amount,refused⟩ | ⟨frames,refused⟩
      · exact reserve_ne_refusal_of_universal_bound available slots n refused
      · exact reserve_ne_refusal_of_universal_bound available frames 1#usize refused
    · rcases refusal with ⟨slots,n,amount,refused⟩ | ⟨arguments,n,amount,refused⟩ | ⟨results,n,amount,refused⟩
      · exact reserve_ne_refusal_of_universal_bound available slots n refused
      · exact reserve_ne_refusal_of_universal_bound available arguments n refused
      · exact reserve_ne_refusal_of_universal_bound available results n refused
  · exact cause

/-- The arguments of a source invocation have the parameter types of its callee. -/
def InvocationArgumentsTyped (store : _root_.store) (address : funcaddr) (args : List val) : Prop :=
  ∀ function params results,store.FUNCS[address]?=some function →
    function.TYPE=.mk_functype (.mk_list params) (.mk_list results) → ResultsTyped store params args

/-- Every source run of an invocation fits the given value and frame limits: the callee
signature and frame, the frame depth of every reachable configuration, and every function
called from a reachable state. Host replies are arbitrary typed values, so this quantifies
over all host behaviors. -/
structure SourceResourcesFit (store : _root_.store) (address : funcaddr) (initial : config)
    (valueLimit frameLimit : Nat) : Prop where
  signature : ∀ function,store.FUNCS[address]?=some function → signatureWords function.TYPE≤valueLimit
  entry : ∀ words,SourceCanonicalFunctionCapacity store address words → words≤valueLimit
  frames : ∀ events final,StepsH initial events final → frameDepth final<frameLimit
  reachable : ∀ events source,StepsH initial events (SourceMachine.decode source) →
    SourceWorldResources valueLimit frameLimit source

theorem CanonicalInvocationResourceCause.excludes_boundary {A M P : Type}
    {allocator : runtime.platform.Alloc A} {hooks : runtime.platform.Platform P M}
    {initial : config} {store : _root_.store} {signature : functype} {address : funcaddr}
    {valueLimit frameLimit : Nat} {error : runtime.ExecError}
    (fits : SourceResourcesFit store address initial valueLimit frameLimit)
    (signatureFits : signatureWords signature≤valueLimit) (initialWf : wf_config initial)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after))
    (cause : CanonicalInvocationResourceCause allocator hooks initial store signature address valueLimit frameLimit error)
    (kind : error=.Terminated ∨ error=.Exhausted .CallStack ∨ error=.Exhausted .Values ∨ error=.Exhausted .Allocation ∨ error=.Exhausted .Objects) : False := by
  rcases kind with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨before,after,refused⟩ := cause
    exact continuing _ _ refused
  · rcases cause with depth | ⟨final,steps,depth⟩
    · have bounded := fits.frames [] initial (StepsH.refl initialWf)
      omega
    · have bounded := fits.frames [] final steps
      omega
  · rcases cause with exceeds | ⟨words,capacity,exceeds⟩ | ⟨source,callee,base,words,steps,site,capacity,exceeds⟩
    · omega
    · have bounded := fits.entry words capacity
      omega
    · have bounded := (fits.reachable [] source steps).defined callee base words site capacity
      omega
  · rcases cause with signatureRefusal | ⟨words,capacity,⟨slots,n,amount,refused⟩ | ⟨frames,refused⟩⟩ |
      ⟨source,steps,callee,base,words,site,capacity,⟨slots,n,amount,refused⟩ | ⟨frames,refused⟩⟩
    · rcases signatureRefusal with ⟨slots,n,amount,refused⟩ | ⟨results,n,amount,refused⟩
      · exact reserve_ne_refusal_of_universal_bound available slots n refused
      · exact reserve_ne_refusal_of_universal_bound available results n refused
    · exact reserve_ne_refusal_of_universal_bound available slots n refused
    · exact reserve_ne_refusal_of_universal_bound available frames 1#usize refused
    · exact reserve_ne_refusal_of_universal_bound available slots n refused
    · exact reserve_ne_refusal_of_universal_bound available frames 1#usize refused
  · exact cause

end Itasca.Runtime.Integration
