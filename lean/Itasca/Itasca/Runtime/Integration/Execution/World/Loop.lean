import Itasca.Runtime.Interp.Recording
import Itasca.Runtime.Integration.Execution.Certificates
import Itasca.Runtime.Integration.Execution.World.State
import Itasca.Runtime.Integration.Execution.Resources.SourceDemand
import Itasca.Runtime.Interp.Relations.StepActive
import Itasca.Runtime.Integration.Execution.Resources.InvocationErrors

/-!
Proofs for Runtime / Integration / Execution / World.

This module collects Reinterpretation, Loop, SourceStep.
Each section documents its contracts and consumers.
-/

/-! ## Reinterpretation -/

section

/-! ## RecordedStep -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Interp

/-- A completed dispatch either constructs its next current-code world or
retains the error's exact returned interpretation, effects and resource cause. -/
def WorldStepResult {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop)
    (before : EventfulWorld M P view expected) (out : EventfulDispatchResult M P) : Prop :=
  match out.1 with
  | .Ok _ => ∃ next : EventfulWorld M P view expected,
      Inv next.code next.machine.store ∧ out=(.Ok (),next.machine.exec,next.machine.store,next.machine.platform) ∧
      EventfulWorldTransition memory hooks floats allocator before
        (stepHostEvents before.machine.exec before.machine.store out) next
  | .Err error => ∃ afterCode,
      Inv afterCode out.2.2.1 ∧ CertifiedSupportedStore view afterCode out.2.2.1 ∧
      Store.MetadataExtended before.machine.store out.2.2.1 ∧
      Store.CodeAgreesOn before.machine.store before.code afterCode ∧
      Extend_store (Representation.decodeStore view before.code before.machine.store) (Representation.decodeStore view afterCode out.2.2.1) ∧
      EventfulInvocationError (SourceMachine.decode before.machine.source)
        (stepHostEvents before.machine.exec before.machine.store out)
        (Representation.decodeStore view afterCode out.2.2.1) before.machine.source.ambient error ∧
      EventfulDispatchCause memory hooks floats allocator before.machine out error

/-- The concrete dispatcher must discharge this interface; it is not an
assumption of a final public theorem. -/
def WorldStepOutcomes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (expected : List valtype)
    (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀ before : EventfulWorld M P view expected,
    Inv before.code before.machine.store → 0<before.machine.exec.frames.length →
    Computation.DivSpec (HostDiverges hooks before.machine.store)
      (runtime.interp.step memory hooks floats allocator before.machine.exec before.machine.store before.machine.platform)
      fun out => WorldStepResult memory hooks floats allocator Inv before out

theorem world_recorded_history {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {expected : List valtype}
    {before after : EventfulWorld M P view expected} {n : Nat} {events : List HostEvent}
    (history : Spec.Iterations (WorldRecordedTransition memory hooks floats allocator) n before events after) :
    Spec.Iterations (EventfulWorldTransition memory hooks floats allocator) n before events after := by
  induction history with
  | refl state => exact .refl state
  | cons edge tail ih => exact .cons edge.edge ih

theorem EventfulWorld.history_ambient {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {expected : List valtype}
    {before after : EventfulWorld M P view expected} {n : Nat} {events : List HostEvent}
    (history : Spec.Iterations (EventfulWorldTransition memory hooks floats allocator) n before events after) :
    after.machine.source.ambient=before.machine.source.ambient := by
  induction history with
  | refl state => rfl
  | cons edge tail ih => exact ih.trans edge.ambient
end Itasca.Integration

end

/-! ## Reinterpretation -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std Itasca.Interp

/-- Reusing a fixed-world successor after reinterpreting only unissued keys
produces a genuine cross-world edge with the original source endpoint. -/
theorem EventfulTransition.world_reinterpret {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {oldCode newCode : Representation.CodeInterpretation} {expected : List valtype}
    {before : EventfulMachine M P view oldCode expected}
    {after : EventfulMachine M P view newCode expected} {events : List WebAssembly.HostEvent}
    (agrees : Store.CodeAgreesOn before.store oldCode newCode)
    (edge : EventfulTransition memory hooks floats allocator (before.change_code newCode agrees) events after) :
    EventfulWorldTransition memory hooks floats allocator ⟨oldCode,before⟩ events ⟨newCode,after⟩ := by
  refine ⟨edge.actual,edge.simulation,?_,edge.metadata,edge.ambient,agrees⟩
  simpa only [EventfulMachine.change_code,Store.decode_store_code_agrees view agrees] using edge.extension
end Itasca.Integration

end

end

/-! ## Loop -/

section

/-!
# Evolving-world loop invariant

The actual interpreter loop preserves a changing ghost code interpretation. Finite histories retain recorder events and actual failures; stopped results retain the source/machine relation.
-/

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Interp

def WorldLoopInvariant {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop)
    (initial : EventfulWorld M P view expected) (state : ExecutionState M P) : Prop :=
  match state.2.2.2 with
  | .Ok _ => ∃ current : EventfulWorld M P view expected,
      Inv current.code current.machine.store ∧ ∃ count events,
      Spec.Iterations (WorldRecordedTransition memory hooks floats allocator) count initial events current ∧
      state.1=current.machine.exec ∧ state.2.1=current.machine.store ∧ state.2.2.1=current.machine.platform
  | .Err error => ∃ current : EventfulWorld M P view expected,
      Inv current.code current.machine.store ∧ ∃ count events,
      Spec.Iterations (WorldRecordedTransition memory hooks floats allocator) count initial events current ∧
      runtime.interp.step memory hooks floats allocator current.machine.exec current.machine.store current.machine.platform=
        .ok (.Err error,state.1,state.2.1,state.2.2.1) ∧
      WorldStepResult memory hooks floats allocator Inv current (.Err error,state.1,state.2.1,state.2.2.1)

theorem world_loop_invariant_step {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop)
    (steps : WorldStepOutcomes memory hooks floats allocator view expected Inv)
    (initial : EventfulWorld M P view expected)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (invariant : WorldLoopInvariant memory hooks floats allocator Inv initial (exec,store,platform,.Ok ()))
    (active : 0<exec.frames.length) :
    runtime.interp.step memory hooks floats allocator exec store platform
      ⦃ (status,nextExec,nextStore,nextPlatform) =>
        WorldLoopInvariant memory hooks floats allocator Inv initial (nextExec,nextStore,nextPlatform,status) ⦄div := by
  obtain ⟨current,valid,count,events,history,sameExec,sameStore,samePlatform⟩ := invariant
  dsimp only at sameExec sameStore samePlatform
  obtain ⟨rfl,rfl,rfl⟩ := And.intro sameExec (And.intro sameStore samePlatform)
  rcases (steps current valid active).imp_exists with
    ⟨⟨status,nextExec,nextStore,nextPlatform⟩,actual,outcome⟩ | ⟨actual,_⟩
  swap
  · rw [actual]
    exact .div _
  rw [actual,WP.dspec_ok]
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
    (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop)
    (steps : WorldStepOutcomes memory hooks floats allocator view expected Inv)
    (initial : EventfulWorld M P view expected) (valid : Inv initial.code initial.machine.store) :
    runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.machine.exec initial.machine.store initial.machine.platform (.Ok ())
      ⦃ result => ∃state,WorldLoopInvariant memory hooks floats allocator Inv initial state ∧
        ¬ActiveExecution state ∧ finishExecution state=result ⦄div := by
  apply execution_loop_stops memory hooks floats allocator
    (WorldLoopInvariant memory hooks floats allocator Inv initial)
    (world_loop_invariant_step memory hooks floats allocator Inv steps initial)
    initial.machine.exec initial.machine.store initial.machine.platform (.Ok ())
  exact ⟨initial,valid,0,[],Spec.Iterations.refl initial,rfl,rfl,rfl⟩

def WorldLoopResult {M P : Type} {view : M → Slice U8} {expected : List valtype}
    (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop)
    (initial : EventfulWorld M P view expected) (result : ExecutionResult M P) : Prop :=
  let finalStore := result.2.2.2.2.2.1
  let status := result.2.2.2.2.2.2.2
  ∃ finalCode,Inv finalCode finalStore ∧ CertifiedSupportedStore view finalCode finalStore ∧
    Store.MetadataExtended initial.machine.store finalStore ∧ Store.CodeAgreesOn initial.machine.store initial.code finalCode ∧
    Extend_store (Representation.decodeStore view initial.code initial.machine.store) (Representation.decodeStore view finalCode finalStore) ∧
    (status=.Ok () → ∃values events,
      ResultsTyped (Representation.decodeStore view finalCode finalStore) expected values ∧
      SourceMachine.Ownership.ValuesOwned (Store.ownershipBounds finalStore) values ∧ ValuesAt result.2.1.val 0 values ∧
      StepsH (SourceMachine.decode initial.machine.source) events
        ⟨⟨Representation.decodeStore view finalCode finalStore,initial.machine.source.ambient⟩,vals values⟩) ∧
    (∀error,status=.Err error → ∃events,EventfulInvocationError (SourceMachine.decode initial.machine.source) events
      (Representation.decodeStore view finalCode finalStore) initial.machine.source.ambient error)

theorem world_loop_finished {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop)
    (initial : EventfulWorld M P view expected) (state : ExecutionState M P)
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
      · simpa only [finishExecution,SourceMachine.decode,sourceEmpty,SourceMachine.decode_frames_nil,current.machine.invariant.storeEq,ambient] using reductions.erase
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
    (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop)
    (steps : WorldStepOutcomes memory hooks floats allocator view expected Inv)
    (initial : EventfulWorld M P view expected) (valid : Inv initial.code initial.machine.store) :
    runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.machine.exec initial.machine.store initial.machine.platform (.Ok ())
      ⦃ result => WorldLoopResult Inv initial result ∧
        ∃state,WorldLoopInvariant memory hooks floats allocator Inv initial state ∧ ¬ActiveExecution state ∧ finishExecution state=result ⦄div := by
  apply WP.dspec_mono (world_loop_stops memory hooks floats allocator Inv steps initial valid)
  rintro result ⟨state,invariant,stopped,same⟩
  exact ⟨same ▸ world_loop_finished memory hooks floats allocator Inv initial state invariant stopped,state,invariant,stopped,same⟩
end Itasca.Integration

end

/-! ## SourceStep -/

section

/-!
# Source-indexed world steps

Bundled and unbundled world-step results retain source points while erased normalization changes the source configuration without executing a raw step.
-/

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Interp

/-- Unbundled source-indexed form of the world result, used while erased
source normalization changes the source point without executing a raw step. -/
def WorldSourceStepResult {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop)
    (code : Representation.CodeInterpretation) (expected : List valtype)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (source : SourceMachine.AState) (pc : Nat) (pending : Bool) (out : EventfulDispatchResult M P) : Prop :=
  match out.1 with
  | .Ok _ => ∃ next : EventfulWorld M P view expected,
      Inv next.code next.machine.store ∧ out=(.Ok (),next.machine.exec,next.machine.store,next.machine.platform) ∧
      EventfulConcreteSim U32.max pc next.machine.pc pending next.machine.pending source next.machine.source
        (stepHostEvents exec store out) ∧
      Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view next.code next.machine.store) ∧
      Store.MetadataExtended store next.machine.store ∧ next.machine.source.ambient=source.ambient ∧
      Store.CodeAgreesOn store code next.code
  | .Err error => ∃ afterCode,
      Inv afterCode out.2.2.1 ∧ CertifiedSupportedStore view afterCode out.2.2.1 ∧
      Store.MetadataExtended store out.2.2.1 ∧ Store.CodeAgreesOn store code afterCode ∧
      Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view afterCode out.2.2.1) ∧
      EventfulInvocationError (SourceMachine.decode source) (stepHostEvents exec store out)
        (Representation.decodeStore view afterCode out.2.2.1) source.ambient error ∧
      ((CumulativeFailure allocator hooks exec store platform source error ∧
        Representation.decodeStore view code out.2.2.1=source.store) ∨
       HostDispatchCause memory hooks floats allocator exec store platform source out error)

theorem WorldStepResult.unbundle {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {expected : List valtype}
    {Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop}
    {before : EventfulWorld M P view expected} {out : EventfulDispatchResult M P}
    (result : WorldStepResult memory hooks floats allocator Inv before out) :
    WorldSourceStepResult (view:=view) memory hooks floats allocator Inv before.code expected before.machine.exec
      before.machine.store before.machine.platform before.machine.source before.machine.pc before.machine.pending out := by
  cases status : out.1 with
  | Ok unit =>
    simp only [WorldStepResult,WorldSourceStepResult,status] at result ⊢
    obtain ⟨next,valid,equal,edge⟩ := result
    exact ⟨next,valid,equal,edge.simulation,edge.extension,edge.metadata,edge.ambient,edge.agrees⟩
  | Err error => simpa only [WorldStepResult,WorldSourceStepResult,status,EventfulDispatchCause] using result

theorem WorldSourceStepResult.bundle {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {expected : List valtype}
    {Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop}
    {before : EventfulWorld M P view expected} {out : EventfulDispatchResult M P}
    (result : WorldSourceStepResult (view:=view) memory hooks floats allocator Inv before.code expected before.machine.exec
      before.machine.store before.machine.platform before.machine.source before.machine.pc before.machine.pending out)
    (actual : runtime.interp.step memory hooks floats allocator before.machine.exec before.machine.store
      before.machine.platform=.ok out) : WorldStepResult memory hooks floats allocator Inv before out := by
  cases status : out.1 with
  | Ok unit =>
    simp only [WorldStepResult,WorldSourceStepResult,status] at result ⊢
    obtain ⟨next,valid,equal,simulation,extension,retained,ambient,agrees⟩ := result
    exact ⟨next,valid,equal,actual.trans (congrArg Result.ok equal),simulation,extension,retained,ambient,agrees⟩
  | Err error => simpa only [WorldStepResult,WorldSourceStepResult,status,EventfulDispatchCause] using result

theorem WorldSourceStepResult.prepend_normalization {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {expected : List valtype}
    {Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop} {code : Representation.CodeInterpretation}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    {count pc : Nat} {s : _root_.store} {ambient : frame} {before middle : SourceMachine.AFrame} {rest : List SourceMachine.AFrame}
    {out : EventfulDispatchResult M P}
    (chain : ErasedSteps count before middle)
    (typed : SourceMachine.ATyped ⟨s,ambient,before::rest,[]⟩)
    (result : WorldSourceStepResult (view:=view)
      memory hooks floats allocator Inv code expected exec store platform ⟨s,ambient,middle::rest,[]⟩ pc false out) :
    WorldSourceStepResult (view:=view)
      memory hooks floats allocator Inv code expected exec store platform ⟨s,ambient,before::rest,[]⟩ pc false out := by
  have normalized := chain.sound s ambient rest typed
  have prefixSteps : StepsH (SourceMachine.decode ⟨s,ambient,before::rest,[]⟩) [] (SourceMachine.decode ⟨s,ambient,middle::rest,[]⟩) := by
    rcases normalized.2 with ⟨rank,same⟩ | simulation
    · simpa only [same] using StepsH.refl typed.decode_wf
    · rcases simulation with ⟨same,decrease⟩ | ⟨n,positive,steps⟩
      · rw [same]
        exact StepsH.refl normalized.1.decode_wf
      · exact steps.erase
  cases status : out.1 with
  | Ok unit =>
    simp only [WorldSourceStepResult,status] at result ⊢
    obtain ⟨next,valid,equal,simulation,extension,retained,ambientEq,agrees⟩ := result
    exact ⟨next,valid,equal,simulation.prepend_normalization chain s ambient rest typed,extension,retained,ambientEq,agrees⟩
  | Err error =>
    simp only [WorldSourceStepResult,status] at result ⊢
    obtain ⟨afterCode,valid,certified,retained,agrees,extension,outcome,cause⟩ := result
    refine ⟨afterCode,valid,certified,retained,agrees,extension,?_,?_⟩
    · simpa only [List.nil_append] using outcome.prepend prefixSteps
    · rcases cause with ⟨failure,decoded⟩ | host
      · exact Or.inl ⟨failure.prepend_normalization chain typed,decoded⟩
      · exact Or.inr (host.prepend prefixSteps rfl rfl)
end Itasca.Integration

end
