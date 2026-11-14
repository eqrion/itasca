import Itasca.Runtime.Integration.Execution.World.Loop
import Itasca.Runtime.Integration.Execution.World.Reinterpretation
import Itasca.Runtime.Integration.Execution.History.State
import Itasca.Runtime.Integration.Execution.Dispatch.Host
import Itasca.Runtime.Integration.Execution.Resources.InvocationErrors
import Itasca.Runtime.Interp.Relations.StepActive
import Itasca.Runtime.Integration.Host.HostRecordingBoundary

/-!
Sections, each formerly its own module: Infinite, NonhostStep.
-/

/-! ## Infinite -/

section

/-!
An actual divergent loop either calls a diverging callback from the current store, or retains its current interpretation and invariant through the next recorded dispatch, including a host publication.

Main declarations: `world_divergent_next` and `world_loop_infinite`. A direct consumer is `Integration.Invocation.DefinedDivergence`.
-/

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Itasca.Runtime.Interp

/-- An actual divergent loop either calls a diverging callback from the current store, or retains
its current interpretation and invariant through the next recorded dispatch, including a host
publication. -/
theorem world_divergent_next {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (steps : WorldStepOutcomes memory hooks floats allocator view expected Inv)
    (before : EventfulWorld M P view expected) (valid : Inv before.code before.machine.store)
    (divergent : runtime.interp.invoke_with_loop1 memory hooks floats allocator before.machine.exec before.machine.store before.machine.platform (.Ok ())=.div) :
    HostDiverges hooks before.machine.store ∨
    ∃events next,WorldRecordedTransition memory hooks floats allocator before events next ∧ Inv next.code next.machine.store ∧
      runtime.interp.invoke_with_loop1 memory hooks floats allocator next.machine.exec next.machine.store next.machine.platform (.Ok ())=.div := by
  have active := execution_loop_divergent_active memory hooks floats allocator before.machine.exec before.machine.store before.machine.platform divergent
  rcases (steps before valid active).imp_exists with
    ⟨⟨status,nextExec,nextStore,nextPlatform⟩,returned,outcome⟩ | ⟨_,diverged⟩
  swap
  · exact Or.inl diverged
  refine Or.inr ?_
  change loop (executionBody memory hooks floats allocator) (before.machine.exec,before.machine.store,before.machine.platform,.Ok ())=.div at divergent
  rw [loop.eq_def,execution_body_active memory hooks floats allocator _ ⟨active,rfl⟩,returned] at divergent
  simp [bind_ok] at divergent
  cases status with
  | Err error => rw [execution_loop_error memory hooks floats allocator] at divergent; simp at divergent
  | Ok value =>
    cases value
    obtain ⟨next,fresh,equal,edge⟩ := outcome
    have components : nextExec=next.machine.exec ∧ nextStore=next.machine.store ∧ nextPlatform=next.machine.platform := by
      simpa only [Prod.mk.injEq,true_and] using equal
    refine ⟨_,next,⟨edge,?_⟩,fresh,?_⟩
    · simp only [components.1,components.2.1,components.2.2]
    · change loop (executionBody memory hooks floats allocator) (next.machine.exec,next.machine.store,next.machine.platform,.Ok ())=.div
      simpa only [components.1,components.2.1,components.2.2] using divergent

/-- Source progress composes across evolving interpretations without a fixed initial or future
set of compiled functions. An actual divergent loop runs the source forever or reaches a world whose
store has a diverging callback. -/
theorem world_loop_infinite {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (steps : WorldStepOutcomes memory hooks floats allocator view expected Inv)
    (initial : EventfulWorld M P view expected) (valid : Inv initial.code initial.machine.store)
    (divergent : runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.machine.exec initial.machine.store initial.machine.platform (.Ok ())=.div) :
    Spec.InfiniteSourceWithEvents (SourceMachine.decode initial.machine.source) ∨
    ∃ (count : Nat) (events : List SpecExt.HostEvent) (reached : EventfulWorld M P view expected),
      Spec.Iterations (WorldRecordedTransition memory hooks floats allocator) count initial events reached ∧
      HostDiverges hooks reached.machine.store := by
  classical
  by_cases host : ∃ (count : Nat) (events : List SpecExt.HostEvent) (reached : EventfulWorld M P view expected),
      Spec.Iterations (WorldRecordedTransition memory hooks floats allocator) count initial events reached ∧
      HostDiverges hooks reached.machine.store
  · exact Or.inr host
  refine Or.inl ?_
  let running := fun state : EventfulWorld M P view expected => Inv state.code state.machine.store ∧
    runtime.interp.invoke_with_loop1 memory hooks floats allocator state.machine.exec state.machine.store state.machine.platform (.Ok ())=.div ∧
    ∃ count events, Spec.Iterations (WorldRecordedTransition memory hooks floats allocator) count initial events state
  let next := fun (before : {s // running s}) events (after : {s // running s}) =>
    WorldRecordedTransition memory hooks floats allocator before.val events after.val
  apply Spec.infinite_source_of_decreasing_stutter next
    (fun s=>SourceMachine.decode s.val.machine.source) (fun s=>s.val.machine.potential) ?_ ?_
    ⟨initial,valid,divergent,0,[],.refl initial⟩
  · intro current
    obtain ⟨fresh,divergent,count,prior,history⟩ := current.property
    rcases world_divergent_next memory hooks floats allocator Inv steps current.val fresh divergent with
      diverged | ⟨events,after,edge,afterValid,afterDivergent⟩
    · exact (host ⟨count,prior,current.val,history,diverged⟩).elim
    · exact ⟨events,⟨after,afterValid,afterDivergent,_,_,history_append history (.cons edge (.refl after))⟩,edge⟩
  · intro before events after edge
    exact edge.edge.simulation
end Itasca.Runtime.Integration

end

/-! ## NonhostStep -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

theorem world_step_or_host
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Store.CodeInterpretation)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (update : ∀code before after,Inv code before → CumulativeStoreMutation view code before after → Inv code after)
    {expected : List valtype} (machine : EventfulMachine M P view code expected)
    (valid : Inv code machine.store)
    (active : 0 < machine.exec.frames.length)
 :
    StructuredHostSite view code machine.exec machine.store expected machine.pc machine.pending machine.source ∨
    runtime.interp.step memory hooks floats allocator machine.exec machine.store machine.platform
      ⦃ out => WorldStepResult memory hooks floats allocator Inv ⟨code,machine⟩ out ⦄ := by
  cases selected : hostStepAddress machine.exec machine.store with
  | some address =>
    exact Or.inl (recording_host_site view code machine.exec machine.store machine.source expected machine.pc machine.pending
      machine.invariant.storeEq machine.certified.shape machine.owned.values machine.invariant active address selected)
  | none =>
    rcases step_supported_host_site memory hooks floats allocator view laws code
      machine.exec machine.store machine.platform machine.source expected machine.pc machine.pending
      machine.invariant.storeEq machine.certified.shape machine.certified.storeSyntax machine.certified.segmentBounds
      machine.certified.compiled machine.certified.typed machine.owned machine.invariant active with host | operation
    · exact Or.inl host
    · apply Or.inr
      obtain ⟨⟨status,exec,store,platform⟩,returned,mutation,outcome⟩ := WP.spec_imp_exists operation
      rw [returned,WP.spec_ok]
      have fresh := machine.certified.update mutation
      have newValid := update code _ _ valid mutation
      cases status with
      | Ok value =>
        cases value
        obtain ⟨pc,pending,source,invariant,simulation,ownership,ambient,bounded⟩ := outcome
        have owned : SourceMachine.Ownership.StatefulOwned (Store.ownershipBounds store) source := by
          rw [mutation.ownership_bounds]
          exact ownership _ machine.owned
        let next : EventfulMachine M P view code expected :=
          ⟨store,exec,platform,source,pc,pending,invariant,fresh,owned⟩
        have edge : EventfulTransition memory hooks floats allocator machine [] next :=
          ⟨returned,simulation.eventful,mutation.extension,mutation.metadata.prefix,ambient⟩
        refine ⟨⟨code,next⟩,newValid,rfl,?_⟩
        simpa only [stepHostEvents,selected] using edge.world
      | Err error =>
        obtain ⟨cause,decoded⟩ := outcome
        refine ⟨code,newValid,fresh,mutation.metadata.prefix,(by intro index inst found fn; rfl),mutation.extension,?_,Or.inl ⟨cause,decoded⟩⟩
        simp only [stepHostEvents,selected]
        rw [decoded]
        exact cause.eventful_error machine.invariant.typed.typed
end Itasca.Runtime.Integration

end
