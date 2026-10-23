import Exec.Theorems.Composition.Eventful.EventfulWorldStep
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

def WorldLoopInvariant {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (initial : EventfulWorld emission allowed M P view expected) (state : ExecutionState M P) : Prop :=
  match state.2.2.2 with
  | .Ok _ => ∃ current : EventfulWorld emission allowed M P view expected,
      Inv current.code current.machine.store ∧ ∃ count events,
      Spec.Iterations (WorldRecordedTransition memory hooks floats allocator) count initial events current ∧
      state.1=current.machine.exec ∧ state.2.1=current.machine.store ∧ state.2.2.1=current.machine.platform
  | .Err error => ∃ current : EventfulWorld emission allowed M P view expected,
      Inv current.code current.machine.store ∧ ∃ count events,
      Spec.Iterations (WorldRecordedTransition memory hooks floats allocator) count initial events current ∧
      runtime.interp.step memory hooks floats allocator current.machine.exec current.machine.store current.machine.platform=
        .ok (.Err error,state.1,state.2.1,state.2.2.1) ∧
      WorldStepResult memory hooks floats allocator Inv current (.Err error,state.1,state.2.1,state.2.2.1)

theorem world_loop_invariant_step {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (steps : WorldStepOutcomes (emission:=emission) (allowed:=allowed) memory hooks floats allocator view expected Inv)
    (initial : EventfulWorld emission allowed M P view expected)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (invariant : WorldLoopInvariant memory hooks floats allocator Inv initial (exec,store,platform,.Ok ()))
    (active : 0<exec.frames.length) :
    runtime.interp.step memory hooks floats allocator exec store platform
      ⦃ (status,nextExec,nextStore,nextPlatform) =>
        WorldLoopInvariant memory hooks floats allocator Inv initial (nextExec,nextStore,nextPlatform,status) ⦄ := by
  obtain ⟨current,valid,count,events,history,sameExec,sameStore,samePlatform⟩ := invariant
  dsimp only at sameExec sameStore samePlatform
  obtain ⟨rfl,rfl,rfl⟩ := And.intro sameExec (And.intro sameStore samePlatform)
  obtain ⟨⟨status,nextExec,nextStore,nextPlatform⟩,actual,outcome⟩ := WP.spec_imp_exists (steps current valid active)
  rw [actual,WP.spec_ok]
  cases status with
  | Ok value =>
    cases value
    obtain ⟨next,fresh,equal,edge⟩ := outcome
    have components : nextExec=next.machine.exec ∧ nextStore=next.machine.store ∧ nextPlatform=next.machine.platform := by
      simpa only [Prod.mk.injEq,true_and] using equal
    let more := stepHostEvents current.machine.exec current.machine.store (.Ok (),nextExec,nextStore,nextPlatform)
    have recorded : WorldRecordedTransition memory hooks floats allocator current more next :=
      ⟨edge,by simp only [more,components.1,components.2.1,components.2.2]⟩
    refine ⟨next,fresh,count+1,events++more,?_,components⟩
    simpa only [List.append_nil] using history_append history (Spec.Iterations.cons recorded (Spec.Iterations.refl next))
  | Err error => exact ⟨current,valid,count,events,history,actual,outcome⟩

/-- The actual loop preserves a changing ghost interpretation. Its finite
history uses the raw recorder's events and retains actual failing dispatches. -/
theorem world_loop_stops {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (steps : WorldStepOutcomes (emission:=emission) (allowed:=allowed) memory hooks floats allocator view expected Inv)
    (initial : EventfulWorld emission allowed M P view expected) (valid : Inv initial.code initial.machine.store) :
    runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.machine.exec initial.machine.store initial.machine.platform (.Ok ())
      ⦃ result => ∃state,WorldLoopInvariant memory hooks floats allocator Inv initial state ∧
        ¬ActiveExecution state ∧ finishExecution state=result ⦄div := by
  apply execution_loop_stops memory hooks floats allocator
    (WorldLoopInvariant memory hooks floats allocator Inv initial)
    (world_loop_invariant_step memory hooks floats allocator Inv steps initial)
    initial.machine.exec initial.machine.store initial.machine.platform (.Ok ())
  exact ⟨initial,valid,0,[],Spec.Iterations.refl initial,rfl,rfl,rfl⟩

def WorldLoopResult {M P : Type} {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (initial : EventfulWorld emission allowed M P view expected) (result : ExecutionResult M P) : Prop :=
  let finalStore := result.2.2.2.2.2.1
  let status := result.2.2.2.2.2.2.2
  ∃ finalCode,Inv finalCode finalStore ∧ CertifiedSupportedStore emission allowed view finalCode finalStore ∧
    FrameStorePrefix initial.machine.store finalStore ∧ Store.CodeAgreesOn initial.machine.store initial.code finalCode ∧
    Extend_store (Store.decodeStore view initial.code initial.machine.store) (Store.decodeStore view finalCode finalStore) ∧
    (status=.Ok () → ∃values events,
      ResultsTyped (Store.decodeStore view finalCode finalStore) expected values ∧
      Abs.Ownership.ValuesOwned (Store.ownershipBounds finalStore) values ∧ ValuesAt result.2.1.val 0 values ∧
      StepsH (Abs.decode initial.machine.source) events
        ⟨⟨Store.decodeStore view finalCode finalStore,initial.machine.source.ambient⟩,vals values⟩) ∧
    (∀error,status=.Err error → ∃events,EventfulInvocationError (Abs.decode initial.machine.source) events
      (Store.decodeStore view finalCode finalStore) initial.machine.source.ambient error)

theorem world_loop_finished {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (initial : EventfulWorld emission allowed M P view expected) (state : ExecutionState M P)
    (invariant : WorldLoopInvariant memory hooks floats allocator Inv initial state)
    (stopped : ¬ActiveExecution state) : WorldLoopResult Inv initial (finishExecution state) := by
  rcases state with ⟨exec,store,platform,status⟩
  cases status with
  | Ok value =>
    cases value
    obtain ⟨current,valid,count,events,history,sameExec,sameStore,samePlatform⟩ := invariant
    dsimp only at sameExec sameStore samePlatform
    obtain ⟨rfl,rfl,rfl⟩ := And.intro sameExec (And.intro sameStore samePlatform)
    have unrecorded := world_recorded_history history
    have metadata := EventfulWorld.history_metadata unrecorded
    have ambient := EventfulWorld.history_ambient unrecorded
    refine ⟨current.code,valid,current.machine.certified,metadata.2.1,metadata.2.2,metadata.1,?_,?_⟩
    · intro success
      have empty : current.machine.exec.frames.val=[] := by
        have length : current.machine.exec.frames.length=0 := by
          simp only [ActiveExecution,true_and,and_true,not_lt] at stopped
          omega
        exact List.length_eq_zero_iff.mp length
      obtain ⟨sourceEmpty,typed,represented⟩ := current.machine.invariant.finished empty
      obtain ⟨n,reductions⟩ := EventfulWorld.history_source unrecorded
      refine ⟨current.machine.source.results,events,?_,current.machine.owned.values.1,represented,?_⟩
      · simpa only [finishExecution,current.machine.invariant.storeEq] using typed
      · simpa only [finishExecution,Abs.decode,sourceEmpty,Abs.decodeFrames_nil,current.machine.invariant.storeEq,ambient] using reductions.erase
    · intro error impossible
      cases impossible
  | Err error =>
    obtain ⟨current,valid,count,events,history,actual,afterCode,fresh,certified,retained,agrees,extension,outcome,cause⟩ := invariant
    have unrecorded := world_recorded_history history
    have metadata := EventfulWorld.history_metadata unrecorded
    have ambient := EventfulWorld.history_ambient unrecorded
    refine ⟨afterCode,fresh,certified,metadata.2.1.trans retained,
      metadata.2.2.trans_prefix metadata.2.1 agrees,Spec.extend_store_trans metadata.1 extension,?_,?_⟩
    · intro impossible
      cases impossible
    · intro reported failed
      have same : error=reported := core.result.Result.Err.inj failed
      subst reported
      obtain ⟨n,reductions⟩ := EventfulWorld.history_source unrecorded
      refine ⟨events++stepHostEvents current.machine.exec current.machine.store (.Err error,exec,store,platform),?_⟩
      simpa only [finishExecution,ambient] using outcome.prepend reductions.erase

theorem world_loop_results {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (steps : WorldStepOutcomes (emission:=emission) (allowed:=allowed) memory hooks floats allocator view expected Inv)
    (initial : EventfulWorld emission allowed M P view expected) (valid : Inv initial.code initial.machine.store) :
    runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.machine.exec initial.machine.store initial.machine.platform (.Ok ())
      ⦃ result => WorldLoopResult Inv initial result ∧
        ∃state,WorldLoopInvariant memory hooks floats allocator Inv initial state ∧ ¬ActiveExecution state ∧ finishExecution state=result ⦄div := by
  apply WP.dspec_mono (world_loop_stops memory hooks floats allocator Inv steps initial valid)
  rintro result ⟨state,invariant,stopped,same⟩
  exact ⟨same ▸ world_loop_finished memory hooks floats allocator Inv initial state invariant stopped,state,invariant,stopped,same⟩
end Exec.Theorems
