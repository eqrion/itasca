import Exec.Theorems.Api.ExecutableInv
import Exec.Theorems.Composition.Eventful.EventfulErrors
import Exec.Spec.Invocation
import Exec.Interp.Relations.FrameStorePrefix

/-! Shared public invocation outcomes and erasure. These predicates retain a
single final code interpretation and sit below the public API constructions. -/
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
/-- Public source correspondence with the full API invariant, including hosts.
Event lists are source witnesses; complete recording-log equality is separate. -/
def ExecutableWorldInvocationOutcome {M P : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (before : runtime.store.Store M)
    (exec : runtime.interp.Execution) (platform : P) (results : alloc.vec.Vec runtime.Value)
    (initial : config)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
      runtime.store.Store M × P × alloc.vec.Vec runtime.Value) : Prop :=
  ∃ afterCode, Store.CodeAgreesOn before code afterCode ∧
  ExecutableInv view afterCode out.2.2.1 ∧ FrameStorePrefix before out.2.2.1 ∧
  Extend_store (Store.decodeStore view code before) (Store.decodeStore view afterCode out.2.2.1) ∧
  (∃events body,StepsH initial events ⟨⟨Store.decodeStore view afterCode out.2.2.1,Spec.invocationFrame⟩,body⟩) ∧
  (out.1=.Ok () → (∃events,StepsH initial events
    ⟨⟨Store.decodeStore view afterCode out.2.2.1,Spec.invocationFrame⟩,vals (out.2.2.2.2.val.map sourceValue)⟩) ∧
    (∀value∈out.2.2.2.2.val,Store.ValueInStore out.2.2.1 value)) ∧
  (∀error,out.1=.Err error →
    ((error=.BadArguments ∨ error=.WrongStore) ∧ out=(.Err error,exec,before,platform,results)) ∨
    ∃events,EventfulInvocationError initial events (Store.decodeStore view afterCode out.2.2.1) Spec.invocationFrame error)

/-- Construct ordinary correspondence from existential source-event evidence.
Unlike recorded construction, this does not require a specified recorder log. -/
theorem ExecutableWorldInvocationOutcome.of_executed {M P : Type}
    {view : M → Slice U8} {code afterCode : Store.CodeInterpretation} {before : runtime.store.Store M}
    {exec : runtime.interp.Execution} {platform : P} {results : alloc.vec.Vec runtime.Value}
    {initial : config} {out}
    (agrees : Store.CodeAgreesOn before code afterCode)
    (retained : ExecutableInv view afterCode out.2.2.1 ∧ FrameStorePrefix before out.2.2.1 ∧
      Extend_store (Store.decodeStore view code before) (Store.decodeStore view afterCode out.2.2.1))
    (success : out.1=.Ok () → (∃events,StepsH initial events
      ⟨⟨Store.decodeStore view afterCode out.2.2.1,Spec.invocationFrame⟩,vals (out.2.2.2.2.val.map sourceValue)⟩) ∧
      (∀value∈out.2.2.2.2.val,Store.ValueInStore out.2.2.1 value))
    (failure : ∀error,out.1=.Err error → ∃events,
      EventfulInvocationError initial events (Store.decodeStore view afterCode out.2.2.1) Spec.invocationFrame error) :
    ExecutableWorldInvocationOutcome view code before exec platform results initial out := by
  refine ⟨afterCode,agrees,retained.1,retained.2.1,retained.2.2,?_,success,fun error failed=>Or.inr (failure error failed)⟩
  cases status : out.1 with
  | Ok value =>
    cases value
    obtain ⟨events,steps⟩ := (success status).1
    exact ⟨events,_,steps⟩
  | Err error =>
    obtain ⟨events,outcome⟩ := failure error status
    obtain ⟨body,steps⟩ := outcome.reachable
    exact ⟨events,body,steps⟩

/-- The retained API/store facts share one chosen final code interpretation. -/
theorem ExecutableWorldInvocationOutcome.retained {M P : Type}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {before : runtime.store.Store M}
    {exec : runtime.interp.Execution} {platform : P} {results : alloc.vec.Vec runtime.Value}
    {initial : config} {out}
    (outcome : ExecutableWorldInvocationOutcome view code before exec platform results initial out) :
    ∃ afterCode, Store.CodeAgreesOn before code afterCode ∧
      ExecutableInv view afterCode out.2.2.1 ∧ FrameStorePrefix before out.2.2.1 ∧
      Extend_store (Store.decodeStore view code before) (Store.decodeStore view afterCode out.2.2.1) := by
  obtain ⟨afterCode,agrees,valid,kept,extension,rest⟩ := outcome
  exact ⟨afterCode,agrees,valid,kept,extension⟩

/-- Public source correspondence at the exact concrete log, allowing callbacks
to publish new code while preserving existing issued instances. -/
def ExecutableWorldRecordedOutcome {M P : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (before : runtime.store.Store M)
    (exec : runtime.interp.Execution) (platform : P) (results : alloc.vec.Vec runtime.Value)
    (initial : config)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
      runtime.store.Store M × P × alloc.vec.Vec runtime.Value) (events : List HostEvent) : Prop :=
  ∃ afterCode, Store.CodeAgreesOn before code afterCode ∧
  ExecutableInv view afterCode out.2.2.1 ∧ FrameStorePrefix before out.2.2.1 ∧
  Extend_store (Store.decodeStore view code before) (Store.decodeStore view afterCode out.2.2.1) ∧
  (∃body,StepsH initial events ⟨⟨Store.decodeStore view afterCode out.2.2.1,Spec.invocationFrame⟩,body⟩) ∧
  (out.1=.Ok () → (StepsH initial events
    ⟨⟨Store.decodeStore view afterCode out.2.2.1,Spec.invocationFrame⟩,vals (out.2.2.2.2.val.map sourceValue)⟩) ∧
    (∀value∈out.2.2.2.2.val,Store.ValueInStore out.2.2.1 value)) ∧
  (∀error,out.1=.Err error →
    ((error=.BadArguments ∨ error=.WrongStore) ∧ out=(.Err error,exec,before,platform,results) ∧ events=[]) ∨
    EventfulInvocationError initial events (Store.decodeStore view afterCode out.2.2.1) Spec.invocationFrame error)

theorem ExecutableWorldRecordedOutcome.of_executed {M P : Type}
    {view : M → Slice U8} {code afterCode : Store.CodeInterpretation} {before : runtime.store.Store M}
    {exec : runtime.interp.Execution} {platform : P} {results : alloc.vec.Vec runtime.Value}
    {initial : config} {out} {events : List HostEvent}
    (agrees : Store.CodeAgreesOn before code afterCode)
    (retained : ExecutableInv view afterCode out.2.2.1 ∧ FrameStorePrefix before out.2.2.1 ∧
      Extend_store (Store.decodeStore view code before) (Store.decodeStore view afterCode out.2.2.1))
    (success : out.1=.Ok () → (StepsH initial events
      ⟨⟨Store.decodeStore view afterCode out.2.2.1,Spec.invocationFrame⟩,vals (out.2.2.2.2.val.map sourceValue)⟩) ∧
      (∀value∈out.2.2.2.2.val,Store.ValueInStore out.2.2.1 value))
    (failure : ∀error,out.1=.Err error →
      EventfulInvocationError initial events (Store.decodeStore view afterCode out.2.2.1) Spec.invocationFrame error) :
    ExecutableWorldRecordedOutcome view code before exec platform results initial out events := by
  refine ⟨afterCode,agrees,retained.1,retained.2.1,retained.2.2,?_,success,fun error failed=>Or.inr (failure error failed)⟩
  cases status : out.1 with
  | Ok value =>
    cases value
    exact ⟨_,(success status).1⟩
  | Err error =>
    have outcome := failure error status
    obtain ⟨body,steps⟩ := outcome.reachable
    exact ⟨body,steps⟩

/-- Forget the recorder equality while retaining the chosen final code world,
source executions, and unchanged-state rejection. -/
theorem ExecutableWorldRecordedOutcome.erase {M P : Type}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {before : runtime.store.Store M}
    {exec : runtime.interp.Execution} {platform : P} {results : alloc.vec.Vec runtime.Value}
    {initial : config} {out} {events : List HostEvent}
    (recorded : ExecutableWorldRecordedOutcome view code before exec platform results initial out events) :
    ExecutableWorldInvocationOutcome view code before exec platform results initial out := by
  obtain ⟨afterCode,agrees,valid,retained,extension,reachable,success,failure⟩ := recorded
  refine ⟨afterCode,agrees,valid,retained,extension,?_,?_,?_⟩
  · obtain ⟨body,steps⟩ := reachable
    exact ⟨events,body,steps⟩
  · intro ok
    exact ⟨⟨events,(success ok).1⟩,(success ok).2⟩
  · intro error failed
    rcases failure error failed with early | execution
    · exact Or.inl ⟨early.1,early.2.1⟩
    · exact Or.inr ⟨events,execution⟩
end Exec.Theorems
