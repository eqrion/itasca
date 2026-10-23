import Exec.Theorems.Api.EventfulInvLoop
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

abbrev EventfulDispatchResult (M P : Type) :=
  core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P

def EventfulCausalStepOutcomes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (expected : List valtype)
    (Inv : runtime.store.Store M → Prop)
    (Cause : EventfulMachine emission allowed M P view code expected → EventfulDispatchResult M P → runtime.ExecError → Prop) : Prop :=
  ∀machine : EventfulMachine emission allowed M P view code expected,Inv machine.store → 0<machine.exec.frames.length →
    runtime.interp.step memory hooks floats allocator machine.exec machine.store machine.platform ⦃ out =>
      Inv out.2.2.1 ∧
      (out.1=.Ok () → ∃events next,out=(.Ok (),next.exec,next.store,next.platform) ∧
        EventfulTransition memory hooks floats allocator machine events next) ∧
      CertifiedSupportedStore emission allowed view code out.2.2.1 ∧
      FrameStorePrefix machine.store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code machine.store) (Store.decodeStore view code out.2.2.1) ∧
      ∀error,out.1=.Err error → ∃events,
        EventfulInvocationError (Abs.decode machine.source) events (Store.decodeStore view code out.2.2.1) machine.source.ambient error ∧
        Cause machine out error ⦄

def EventfulCausalLoopInvariant {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (Inv : runtime.store.Store M → Prop)
    (Cause : EventfulMachine emission allowed M P view code expected → EventfulDispatchResult M P → runtime.ExecError → Prop)
    (initial : EventfulMachine emission allowed M P view code expected) (state : ExecutionState M P) : Prop :=
  Inv state.2.1 ∧ CertifiedSupportedStore emission allowed view code state.2.1 ∧
  FrameStorePrefix initial.store state.2.1 ∧
  Extend_store (Store.decodeStore view code initial.store) (Store.decodeStore view code state.2.1) ∧
  match state.2.2.2 with
  | .Ok _ => ∃machine count events,
      Spec.Iterations (EventfulTransition memory hooks floats allocator) count initial events machine ∧
      state.1=machine.exec ∧ state.2.1=machine.store ∧ state.2.2.1=machine.platform
  | .Err error => ∃machine count events rest,
      Spec.Iterations (EventfulTransition memory hooks floats allocator) count initial events machine ∧
      runtime.interp.step memory hooks floats allocator machine.exec machine.store machine.platform =
        .ok (.Err error,state.1,state.2.1,state.2.2.1) ∧
      EventfulInvocationError (Abs.decode machine.source) rest (Store.decodeStore view code state.2.1) machine.source.ambient error ∧
      Inv machine.store ∧ Cause machine (.Err error,state.1,state.2.1,state.2.2.1) error

theorem EventfulCausalLoopInvariant.erase {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {Inv : runtime.store.Store M → Prop}
    {Cause : EventfulMachine emission allowed M P view code expected → EventfulDispatchResult M P → runtime.ExecError → Prop}
    {initial : EventfulMachine emission allowed M P view code expected} {state : ExecutionState M P}
    (invariant : EventfulCausalLoopInvariant memory hooks floats allocator Inv Cause initial state) :
    Inv state.2.1 ∧ EventfulLoopInvariant memory hooks floats allocator initial state := by
  obtain ⟨valid,certified,metadata,extension,outcome⟩ := invariant
  refine ⟨valid,certified,metadata,extension,?_⟩
  cases status : state.2.2.2 with
  | Ok value => simpa only [status] using outcome
  | Err error =>
    simp only [status] at outcome ⊢
    obtain ⟨machine,count,events,rest,history,actual,source,valid,cause⟩ := outcome
    exact ⟨machine,count,events,rest,history,actual,source⟩

theorem eventful_causal_loop_invariant_step {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (Inv : runtime.store.Store M → Prop)
    (Cause : EventfulMachine emission allowed M P view code expected → EventfulDispatchResult M P → runtime.ExecError → Prop)
    (steps : EventfulCausalStepOutcomes (emission:=emission) (allowed:=allowed) memory hooks floats allocator view code expected Inv Cause)
    (initial : EventfulMachine emission allowed M P view code expected)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (invariant : EventfulCausalLoopInvariant memory hooks floats allocator Inv Cause initial (exec,store,platform,.Ok ()))
    (active : 0<exec.frames.length) :
    runtime.interp.step memory hooks floats allocator exec store platform
      ⦃ (status,nextExec,nextStore,nextPlatform) =>
        EventfulCausalLoopInvariant memory hooks floats allocator Inv Cause initial (nextExec,nextStore,nextPlatform,status) ⦄ := by
  obtain ⟨valid,certified,retainedBefore,extension,machine,count,events,history,sameExec,sameStore,samePlatform⟩ := invariant
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
    obtain ⟨more,outcome,cause⟩ := failed error rfl
    exact ⟨machine,count,events,more,history,actual,outcome,valid,cause⟩

/-- A reported loop error is backed by its actual reached invariant-bearing
machine, successful concrete/source prefix, and the actual failing dispatch. -/
def EventfulLoopFailure {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (Inv : runtime.store.Store M → Prop)
    (Cause : EventfulMachine emission allowed M P view code expected → EventfulDispatchResult M P → runtime.ExecError → Prop)
    (initial : EventfulMachine emission allowed M P view code expected) (result : ExecutionResult M P) (error : runtime.ExecError) : Prop :=
  ∃previous count events afterExec afterStore afterPlatform,
    Spec.Iterations (EventfulTransition memory hooks floats allocator) count initial events previous ∧
    Inv previous.store ∧ runtime.interp.step memory hooks floats allocator previous.exec previous.store previous.platform =
      .ok (.Err error,afterExec,afterStore,afterPlatform) ∧
    Cause previous (.Err error,afterExec,afterStore,afterPlatform) error ∧
    finishExecution (afterExec,afterStore,afterPlatform,.Err error)=result

theorem eventful_causal_loop_results {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (Inv : runtime.store.Store M → Prop)
    (Cause : EventfulMachine emission allowed M P view code expected → EventfulDispatchResult M P → runtime.ExecError → Prop)
    (steps : EventfulCausalStepOutcomes (emission:=emission) (allowed:=allowed) memory hooks floats allocator view code expected Inv Cause)
    (initial : EventfulMachine emission allowed M P view code expected) (valid : Inv initial.store) :
    runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())
      ⦃ result => Inv result.2.2.2.2.2.1 ∧ EventfulLoopResult initial result ∧
        ∀error,result.2.2.2.2.2.2.2=.Err error → EventfulLoopFailure memory hooks floats allocator Inv Cause initial result error ⦄div := by
  apply WP.dspec_mono (execution_loop_stops memory hooks floats allocator
    (EventfulCausalLoopInvariant memory hooks floats allocator Inv Cause initial)
    (eventful_causal_loop_invariant_step memory hooks floats allocator Inv Cause steps initial)
    initial.exec initial.store initial.platform (.Ok ()) ?_)
  · rintro result ⟨state,invariant,stopped,same⟩
    rw [←same]
    have erased := invariant.erase
    refine ⟨erased.1,eventful_loop_finished memory hooks floats allocator initial state erased.2 stopped,?_⟩
    intro error failed
    rcases state with ⟨exec,store,platform,status⟩
    change status=.Err error at failed
    subst status
    obtain ⟨valid,certified,metadata,extension,previous,count,events,rest,history,actual,source,previousValid,cause⟩ := invariant
    exact ⟨previous,count,events,exec,store,platform,history,previousValid,actual,cause,rfl⟩
  · exact ⟨valid,initial.certified,.refl _,Spec.extend_store_refl _
      (Store.decodeStore_wf view code _ initial.certified.shape initial.certified.storeSyntax),
      initial,0,[],Spec.Iterations.refl initial,rfl,rfl,rfl⟩
end Exec.Theorems
