import Exec.Theorems.Host.HostReadyUniform
import Exec.Theorems.Composition.Uniform.UniformSupportedTransport
import Exec.Interp.Relations.EventfulNormalize
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

/-- All normalized direct and indirect host sites return normally. Successful
results retain the exact eventful advance, including source-only prefixes. The
raw retention and issuance premises are explicit conditional embedding laws. -/
theorem StructuredHostSite.uniform_invariant_success {M P F A : Type}
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
      Inv out.2.2.1 ∧ (out.1=.Ok () → ∃ events, ∃ next : EventfulMachine emission allowed M P view code expected,
        out=(.Ok (),next.exec,next.store,next.platform) ∧
        EventfulConcreteSim U32.max pc next.pc pending next.pending source next.source events ∧
        UniformConcreteSim pc next.pc pending next.pending source next.source events ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view code next.store) ∧
        FrameStorePrefix store next.store ∧ next.source.ambient=source.ambient) ⦄ := by
  induction site with
  | @ready ambient f rest op after site kind =>
    apply WP.spec_mono (host_ready_uniform_invariant_success memory hooks floats allocator allocation interrupts view code Inv certify sound
      exec store platform valid expected ambient f rest op after site kind (fun p host => preserve host p) (fun p host => externs host p) (fun p host => issued host p))
    intro out result
    refine ⟨result.1,?_⟩
    intro success
    obtain ⟨events,next,equal,edge⟩ := result.2 success
    exact ⟨events,next,equal,edge.simulation,edge.uniform,edge.extension,edge.metadata,edge.ambient⟩
  | @normalize count pc s ambient before middle rest chain site ih =>
    apply WP.spec_mono (ih (chain.sound s ambient rest typed).1)
    intro out result
    refine ⟨result.1,?_⟩
    intro success
    obtain ⟨events,next,equal,simulation,uniform,extension,metadata,ambientEq⟩ := result.2 success
    exact ⟨events,next,equal,simulation.prepend_normalization chain s ambient rest typed,
      uniform.prepend_normalization chain s ambient rest typed,
      extension,metadata,ambientEq⟩
end Exec.Theorems
