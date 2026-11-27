import Itasca.Results.Definitions.Runtime
import Itasca.Runtime.Platform.Observation

/-! # Callback laws under observation

The observer records a boundary that already exists. It adds no callback
premises and does not restrict how a callback extends the store or chooses
its next ghost interpretation.
-/
namespace Itasca.Integration
open Aeneas Aeneas.Std Itasca.Platform

/-- The same source-store and ownership laws hold for the observing wrapper. -/
theorem HostLaws.observing {M P : Type}
    {hooks : runtime.platform.Platform P M} {view : M → Slice U8}
    {Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop}
    (laws : HostLaws hooks view Inv) : HostLaws (observing hooks) view Inv := by
  intro code store valid platform identity args defaults
  rcases platform with ⟨platform, prior⟩
  unfold Platform.observing
  step with laws code store valid platform identity args defaults
    as ⟨status, next, after, returned, afterCode, post⟩
  rw [WP.dspec_ok]
  exact ⟨afterCode, post⟩

end Itasca.Integration

namespace Itasca.Integration
open Aeneas Aeneas.Std Itasca.Platform WebAssembly

/-- Internal evidence for a host call's callback boundary. The interrupt may
reject preparation; otherwise exactly one raw callback supplies the event.
Unlike an outcome classifier, this evidence retains the actual hook equations. -/
def HostCallBoundary {M P : Type} (hooks : runtime.platform.Platform P M)
    (store : runtime.store.Store M) (platform : P) (identity : U64)
    (after : runtime.store.Store M) (nextPlatform : P) (events : List HostEvent) : Prop :=
  ∃ decision middle, hooks.interrupt platform = .ok (decision, middle) ∧
    ((nextPlatform = middle ∧ events = []) ∨
      ∃ args defaults status returned,
        hooks.call_host middle store identity args defaults = .ok (status, nextPlatform, after, returned) ∧
        List.Forall₂ HostObservation.Matches
          [⟨store, identity, args, defaults, status, after, returned⟩] events)

/-- Boundary evidence identifies the exact appended log, including the empty
log for a rejection before the callback. Source addresses come only from the
matching source events, never from the observer. -/
theorem HostCallBoundary.observing {M P : Type}
    {hooks : runtime.platform.Platform P M} {store after : runtime.store.Store M}
    {platform nextPlatform : P} {prior trace : List (HostObservation M)}
    {identity : U64} {events : List HostEvent}
    (boundary : HostCallBoundary (observing hooks) store (platform, prior) identity
      after (nextPlatform, trace) events) :
    ∃ observations, trace = prior ++ observations ∧
      List.Forall₂ HostObservation.Matches observations events := by
  obtain ⟨decision, ⟨middle, middleTrace⟩, interrupted, boundary⟩ := boundary
  have erased := observing_interrupt_erase hooks platform prior
  rw [interrupted, bind_ok] at erased
  have actual : hooks.interrupt platform = .ok (decision, middle) := erased.symm
  have same : middleTrace = prior := by
    simpa only [Platform.observing, actual, bind_ok, Std.uncurry, Result.ok.injEq,
      Prod.mk.injEq, true_and] using interrupted.symm
  subst middleTrace
  rcases boundary with ⟨same, rfl⟩ | ⟨args, defaults, status, returned, called, matched⟩
  · have sameTrace := congrArg Prod.snd same
    exact ⟨[], by simpa only [List.append_nil] using sameTrace, .nil⟩
  · exact ⟨_, ((observing_call_returned ..).mp called).2, matched⟩

end Itasca.Integration
