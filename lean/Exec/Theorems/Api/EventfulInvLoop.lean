import Exec.Theorems.Composition.Eventful.EventfulLoopOutcomes
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

def EventfulInvStepOutcomes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (expected : List valtype)
    (Inv : runtime.store.Store M → Prop) : Prop :=
  ∀ machine : EventfulMachine emission allowed M P view code expected, Inv machine.store → 0<machine.exec.frames.length →
    runtime.interp.step memory hooks floats allocator machine.exec machine.store machine.platform ⦃ out =>
      Inv out.2.2.1 ∧
      (out.1=.Ok () → ∃events next,out=(.Ok (),next.exec,next.store,next.platform) ∧
        EventfulTransition memory hooks floats allocator machine events next) ∧
      CertifiedSupportedStore emission allowed view code out.2.2.1 ∧
      FrameStorePrefix machine.store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code machine.store) (Store.decodeStore view code out.2.2.1) ∧
      ∀error,out.1=.Err error → ∃events,
        EventfulInvocationError (Abs.decode machine.source) events
          (Store.decodeStore view code out.2.2.1) machine.source.ambient error ⦄

theorem eventful_inv_loop_invariant_step {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (Inv : runtime.store.Store M → Prop)
    (steps : EventfulInvStepOutcomes (emission:=emission) (allowed:=allowed) memory hooks floats allocator view code expected Inv)
    (initial : EventfulMachine emission allowed M P view code expected)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (invariant : Inv store ∧ EventfulLoopInvariant memory hooks floats allocator initial (exec,store,platform,.Ok ()))
    (active : 0<exec.frames.length) :
    runtime.interp.step memory hooks floats allocator exec store platform
      ⦃ (status,nextExec,nextStore,nextPlatform) =>
        Inv nextStore ∧ EventfulLoopInvariant memory hooks floats allocator initial (nextExec,nextStore,nextPlatform,status) ⦄ := by
  obtain ⟨valid,invariant⟩ := invariant
  obtain ⟨certified,retainedBefore,extension,machine,count,events,history,sameExec,sameStore,samePlatform⟩ := invariant
  dsimp only at sameExec sameStore samePlatform
  obtain ⟨rfl,rfl,rfl⟩ := And.intro sameExec (And.intro sameStore samePlatform)
  obtain ⟨⟨status,nextExec,nextStore,nextPlatform⟩,actual,newValid,success,fresh,retained,growth,failed⟩ := WP.spec_imp_exists (steps machine valid active)
  rw [actual,WP.spec_ok]
  refine ⟨newValid,fresh,retainedBefore.trans retained,Spec.extend_store_trans extension growth,?_⟩
  cases status with
  | Ok value =>
    cases value
    obtain ⟨more,next,equal,edge⟩ := success rfl
    have components : nextExec=next.exec ∧ nextStore=next.store ∧ nextPlatform=next.platform := by
      simpa only [Prod.mk.injEq,true_and] using equal
    refine ⟨next,count+1,events++more,?_,components⟩
    simpa only [List.append_nil] using history_append history (Spec.Iterations.cons edge (Spec.Iterations.refl next))
  | Err error =>
    obtain ⟨more,outcome⟩ := failed error rfl
    exact ⟨machine,count,events,more,history,actual,outcome⟩

/-- An auxiliary store invariant is preserved through the actual host-capable
loop. Concrete dispatch must discharge its local preservation obligation. -/
theorem eventful_inv_loop_results {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (Inv : runtime.store.Store M → Prop)
    (steps : EventfulInvStepOutcomes (emission:=emission) (allowed:=allowed) memory hooks floats allocator view code expected Inv)
    (initial : EventfulMachine emission allowed M P view code expected) (valid : Inv initial.store) :
    runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())
      ⦃ result => Inv result.2.2.2.2.2.1 ∧ EventfulLoopResult initial result ⦄div := by
  let loopInv := fun (state : ExecutionState M P) => Inv state.2.1 ∧ EventfulLoopInvariant memory hooks floats allocator initial state
  apply WP.dspec_mono (execution_loop_stops memory hooks floats allocator loopInv
    (eventful_inv_loop_invariant_step memory hooks floats allocator Inv steps initial)
    initial.exec initial.store initial.platform (.Ok ()) ?_)
  · rintro result ⟨state,⟨valid,invariant⟩,stopped,same⟩
    rw [←same]
    exact ⟨valid,eventful_loop_finished memory hooks floats allocator initial state invariant stopped⟩
  · exact ⟨valid,initial.certified,.refl _,Spec.extend_store_refl _
      (Store.decodeStore_wf view code _ initial.certified.shape initial.certified.storeSyntax),
      initial,0,[],Spec.Iterations.refl initial,rfl,rfl,rfl⟩
end Exec.Theorems
