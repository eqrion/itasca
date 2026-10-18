import Exec.Theorems.Host.HostReadyEventfulInvariantEffects
import Exec.Interp.Relations.EventfulNormalize
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

/-- Normalize source control before retaining the actual host-call error and store effects. -/
theorem StructuredHostSite.eventful_invariant_effects {M P F A : Type}
    {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
    [∀ compiled, StructuredMachine.OrdinaryHeads (emission compiled)]
    [∀ compiled, StructuredMachine.IndirectProjection (emission compiled) compiled.indirect.val]
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (Inv : runtime.store.Store M → Prop)
    (certify : ∀s,Inv s → CertifiedSupportedStore emission allowed view code s)
    (sound : Platform.HostSound hooks Inv (Store.decodeStore view code))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv store)
    (preserve : ∀ host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀ host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀ host p args results answer,
      hooks.call_host p store host args results=.ok answer →
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    {expected : List valtype} {pc : Nat} {pending : Bool} {source : Abs.AState}
    (site : StructuredHostSite emission allowed view code exec store expected pc pending source)
    (typed : Abs.ATyped source) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      Inv out.2.2.1 ∧ CertifiedSupportedStore emission allowed view code out.2.2.1 ∧
      FrameStorePrefix store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
      ∀error,out.1=.Err error → ∃events,
        EventfulInvocationError (Abs.decode source) events
          (Store.decodeStore view code out.2.2.1) source.ambient error ⦄ := by
  induction site with
  | @ready ambient f rest op after site kind =>
    exact host_ready_eventful_invariant_effects memory hooks floats allocator allocation interrupts view code Inv certify sound
      exec store platform valid expected ambient f rest op after site kind
      (fun p host=>preserve host p) (fun p host=>externs host p) (fun p host=>issued host p)
  | @normalize count pc s ambient before middle rest chain site ih =>
    have normalized := chain.sound s ambient rest typed
    apply WP.spec_mono (ih normalized.1)
    intro out result
    obtain ⟨newValid,result⟩ := result
    refine ⟨newValid,result.1,result.2.1,result.2.2.1,?_⟩
    intro error failed
    obtain ⟨events,outcome⟩ := result.2.2.2 error failed
    refine ⟨events,?_⟩
    rcases normalized.2 with ⟨rank,same⟩ | simulation
    · simpa only [same] using outcome
    · rcases simulation with ⟨same,decrease⟩ | ⟨n,positive,steps⟩
      · simpa only [same] using outcome
      · simpa only [List.nil_append] using outcome.prepend steps.erase
end Exec.Theorems
