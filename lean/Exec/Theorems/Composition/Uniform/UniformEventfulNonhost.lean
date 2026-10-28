import Exec.Theorems.Composition.Uniform.UniformSupportedDispatch
import Exec.Theorems.Composition.Uniform.UniformEventfulHistory
import Exec.Theorems.Composition.Eventful.EventfulErrors
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

theorem uniform_eventful_inv_step_or_host
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Store.CodeInterpretation)
    (Inv : runtime.store.Store M → Prop)
    (update : ∀before after,Inv before → CumulativeStoreMutation view code before after → Inv after)
    {expected : List valtype} (machine : EventfulMachine M P view code expected)
    (valid : Inv machine.store)
    (active : 0 < machine.exec.frames.length) :
    StructuredHostSite view code machine.exec machine.store expected machine.pc machine.pending machine.source ∨
    runtime.interp.step memory hooks floats allocator machine.exec machine.store machine.platform ⦃ out =>
      Inv out.2.2.1 ∧
      (out.1=.Ok () → ∃events next,out=(.Ok (),next.exec,next.store,next.platform) ∧
        UniformEventfulTransition memory hooks floats allocator machine events next) ∧
      CertifiedSupportedStore view code out.2.2.1 ∧
      FrameStorePrefix machine.store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code machine.store) (Store.decodeStore view code out.2.2.1) ∧
      ∀error,out.1=.Err error → ∃events,
        EventfulInvocationError (Abs.decode machine.source) events
          (Store.decodeStore view code out.2.2.1) machine.source.ambient error ⦄ := by
  rcases step_supported_host_site_uniform memory hooks floats allocator view laws code
    machine.exec machine.store machine.platform machine.source expected machine.pc machine.pending
    machine.invariant.storeEq machine.certified.shape machine.certified.storeSyntax machine.certified.segmentBounds
    machine.certified.compiled machine.certified.typed machine.owned machine.invariant active with host | operation
  · exact Or.inl host
  · apply Or.inr
    obtain ⟨⟨status,exec,store,platform⟩,returned,mutation,outcome⟩ := WP.spec_imp_exists operation
    rw [returned,WP.spec_ok]
    have fresh := machine.certified.update mutation
    refine ⟨update _ _ valid mutation,?_,fresh,mutation.metadata.prefix,mutation.extension,?_⟩
    · intro success
      change status=.Ok () at success
      subst status
      obtain ⟨pc,pending,source,invariant,simulation,uniform,ownership,ambient,bounded⟩ := outcome
      have owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store) source := by
        rw [mutation.ownership_bounds]
        exact ownership _ machine.owned
      let next : EventfulMachine M P view code expected :=
        ⟨store,exec,platform,source,pc,pending,invariant,fresh,owned⟩
      exact ⟨[],next,rfl,⟨returned,simulation.eventful,mutation.extension,mutation.metadata.prefix,ambient⟩,uniform⟩
    · intro error failed
      change status=.Err error at failed
      subst status
      obtain ⟨cause,decoded⟩ := outcome
      refine ⟨[],?_⟩
      rw [decoded]
      exact cause.eventful_error machine.invariant.typed.typed
end Exec.Theorems
