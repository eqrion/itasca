import Exec.Theorems.Composition.Eventful.EventfulStepOutcomes
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Finite execution retains its concrete successful dispatch history. An error
also retains the actual failing dispatch and its labeled source endpoint. -/
def EventfulLoopInvariant {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (initial : EventfulMachine emission allowed M P view code expected) (state : ExecutionState M P) : Prop :=
  CertifiedSupportedStore emission allowed view code state.2.1 ∧
  FrameStorePrefix initial.store state.2.1 ∧
  Extend_store (Store.decodeStore view code initial.store) (Store.decodeStore view code state.2.1) ∧
  match state.2.2.2 with
  | .Ok _ => ∃ machine count events,
      Spec.Iterations (EventfulTransition memory hooks floats allocator) count initial events machine ∧
      state.1=machine.exec ∧ state.2.1=machine.store ∧ state.2.2.1=machine.platform
  | .Err error => ∃ machine count events rest,
      Spec.Iterations (EventfulTransition memory hooks floats allocator) count initial events machine ∧
      runtime.interp.step memory hooks floats allocator machine.exec machine.store machine.platform =
        .ok (.Err error,state.1,state.2.1,state.2.2.1) ∧
      EventfulInvocationError (Abs.decode machine.source) rest
        (Store.decodeStore view code state.2.1) machine.source.ambient error

theorem eventful_loop_invariant_step {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (steps : EventfulStepOutcomes (emission:=emission) (allowed:=allowed) memory hooks floats allocator view code expected)
    (initial : EventfulMachine emission allowed M P view code expected)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (invariant : EventfulLoopInvariant memory hooks floats allocator initial (exec,store,platform,.Ok ()))
    (active : 0<exec.frames.length) :
    runtime.interp.step memory hooks floats allocator exec store platform
      ⦃ (status,nextExec,nextStore,nextPlatform) =>
        EventfulLoopInvariant memory hooks floats allocator initial (nextExec,nextStore,nextPlatform,status) ⦄ := by
  obtain ⟨certified,retainedBefore,extension,machine,count,events,history,sameExec,sameStore,samePlatform⟩ := invariant
  dsimp only at sameExec sameStore samePlatform
  obtain ⟨rfl,rfl,rfl⟩ := And.intro sameExec (And.intro sameStore samePlatform)
  obtain ⟨⟨status,nextExec,nextStore,nextPlatform⟩,actual,success,fresh,retained,growth,failed⟩ := WP.spec_imp_exists (steps machine active)
  rw [actual,WP.spec_ok]
  refine ⟨fresh,retainedBefore.trans retained,Spec.extend_store_trans extension growth,?_⟩
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

/-- Actual normal loop exits retain the source history and the exact final
store, while infinite execution remains allowed. -/
theorem eventful_loop_stops {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (steps : EventfulStepOutcomes (emission:=emission) (allowed:=allowed) memory hooks floats allocator view code expected)
    (initial : EventfulMachine emission allowed M P view code expected) :
    runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())
      ⦃ result => ∃state, EventfulLoopInvariant memory hooks floats allocator initial state ∧
        ¬ActiveExecution state ∧ finishExecution state=result ⦄div := by
  apply execution_loop_stops memory hooks floats allocator
    (EventfulLoopInvariant memory hooks floats allocator initial)
    (eventful_loop_invariant_step memory hooks floats allocator steps initial)
    initial.exec initial.store initial.platform (.Ok ())
  exact ⟨initial.certified,.refl _,Spec.extend_store_refl _ (Store.decodeStore_wf view code _ initial.certified.shape initial.certified.storeSyntax),
    initial,0,[],Spec.Iterations.refl initial,rfl,rfl,rfl⟩

/-- The readback facts needed by public invocation, together with source
results or an exact reached-store error. Event labels here are source traces;
recording-log correspondence is a separate obligation. -/
def EventfulLoopResult {M P view code expected}
    (initial : EventfulMachine emission allowed M P view code expected) (result : ExecutionResult M P) : Prop :=
  let finalStore := result.2.2.2.2.2.1
  let status := result.2.2.2.2.2.2.2
  CertifiedSupportedStore emission allowed view code finalStore ∧
  FrameStorePrefix initial.store finalStore ∧
  Extend_store (Store.decodeStore view code initial.store) (Store.decodeStore view code finalStore) ∧
  (status=.Ok () → ∃values events,
    ResultsTyped (Store.decodeStore view code finalStore) expected values ∧
    Abs.Ownership.ValuesOwned (Store.ownershipBounds finalStore) values ∧
    ValuesAt result.2.1.val 0 values ∧
    StepsH (Abs.decode initial.source) events
      ⟨⟨Store.decodeStore view code finalStore,initial.source.ambient⟩,vals values⟩) ∧
  (∀error,status=.Err error → ∃events,
    EventfulInvocationError (Abs.decode initial.source) events
      (Store.decodeStore view code finalStore) initial.source.ambient error)

theorem eventful_loop_finished {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (initial : EventfulMachine emission allowed M P view code expected) (state : ExecutionState M P)
    (invariant : EventfulLoopInvariant memory hooks floats allocator initial state)
    (stopped : ¬ActiveExecution state) :
    EventfulLoopResult initial (finishExecution state) := by
  rcases state with ⟨exec,store,platform,status⟩
  obtain ⟨certified,retainedBefore,extension,invariant⟩ := invariant
  refine ⟨certified,retainedBefore,extension,?_,?_⟩
  · intro success
    change status=.Ok () at success
    subst status
    obtain ⟨machine,dispatches,events,history,sameExec,sameStore,samePlatform⟩ := invariant
    dsimp only at sameExec sameStore samePlatform
    obtain ⟨rfl,rfl,rfl⟩ := And.intro sameExec (And.intro sameStore samePlatform)
    have empty : machine.exec.frames.val=[] := by
      have length : machine.exec.frames.length=0 := by
        simp only [ActiveExecution,true_and,and_true,not_lt] at stopped
        omega
      exact List.length_eq_zero_iff.mp length
    obtain ⟨sourceEmpty,typed,represented⟩ := machine.invariant.finished empty
    obtain ⟨count,reductions⟩ := EventfulMachine.history_source history
    have ambient := (EventfulMachine.history_metadata history).2.2
    refine ⟨machine.source.results,events,?_,machine.owned.values.1,represented,?_⟩
    · simpa only [finishExecution,machine.invariant.storeEq] using typed
    · simpa only [finishExecution,Abs.decode,sourceEmpty,Abs.decodeFrames_nil,machine.invariant.storeEq,ambient] using reductions.erase
  · intro error failed
    change status=.Err error at failed
    subst status
    obtain ⟨machine,dispatches,events,more,history,actual,outcome⟩ := invariant
    obtain ⟨count,reductions⟩ := EventfulMachine.history_source history
    have ambient := (EventfulMachine.history_metadata history).2.2
    refine ⟨events++more,?_⟩
    simpa only [finishExecution,ambient] using outcome.prepend reductions.erase

theorem eventful_loop_results {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (steps : EventfulStepOutcomes (emission:=emission) (allowed:=allowed) memory hooks floats allocator view code expected)
    (initial : EventfulMachine emission allowed M P view code expected) :
    runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())
      ⦃ result => EventfulLoopResult initial result ⦄div := by
  apply WP.dspec_mono (eventful_loop_stops memory hooks floats allocator steps initial)
  rintro result ⟨state,invariant,stopped,same⟩
  rw [←same]
  exact eventful_loop_finished memory hooks floats allocator initial state invariant stopped
end Exec.Theorems
