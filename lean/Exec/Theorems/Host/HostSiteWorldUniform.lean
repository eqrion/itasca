import Exec.Theorems.Host.HostReadyWorldUniform
import Exec.Interp.Relations.EventfulNormalize
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

/-- All normalized direct and indirect host sites return normally. Successful
results retain the exact eventful advance, including source-only prefixes. The
raw retention and issuance premises are explicit conditional embedding laws. -/
theorem StructuredHostSite.world_uniform {M P F A : Type}

    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀ c s,Inv c s → CertifiedSupportedStore view c s)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv code store)
    (callback : ∀ host p args results,
      hooks.call_host p store host args results ⦃ answer => ∃ afterCode,
        Store.CodeAgreesOn store code afterCode ∧ Inv afterCode answer.2.2.1 ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode answer.2.2.1) ∧
        Store_ok (Store.decodeStore view afterCode answer.2.2.1) ⦄)
    (retains : ∀ host, HostRetention hooks store host)
    {expected : List valtype} {pc : Nat} {pending : Bool} {source : Abs.AState}
    (site : StructuredHostSite view code exec store expected pc pending source)
    (typed : Abs.ATyped source) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      UniformWorldSourceSuccess (view:=view)
        Inv code expected store source pc pending out ⦄ := by
  induction site with
  | @ready ambient f rest op after site kind =>
    exact host_ready_world_uniform memory hooks floats allocator allocation interrupts view code Inv certify
      exec store platform valid expected ambient f rest op after site kind
      (fun p host => callback host p) retains
  | @normalize count pc s ambient before middle rest chain site ih =>
    apply WP.spec_mono (ih (chain.sound s ambient rest typed).1)
    intro out result
    exact result.prepend_normalization chain typed
end Exec.Theorems
