import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Source.Control.Publication
import Exec.Theorems.Host.Open.Driver.DriverTick
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Checked local effects give the same cross-world effect used by suspended
callers, with unchanged code and external-reference issuance. -/
theorem local_effect_world {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {before after : runtime.store.Store M} (effect : OpenHostControl.Effect view code before after) :
    ReentrantCallbacks.Effect view code before code after :=
  ⟨⟨(by intro index inst found fn; rfl),effect.invariant,effect.metadata,effect.extension⟩,by rw [effect.externs]⟩

/-- One actual local host tick advances the independent source control once.
The whole suspended stack is transported through its committed effect. -/
theorem source_local_step {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (code : Store.CodeInterpretation) (native : State M) (source : Spec.OpenExecution.State SourceControl) (rank : Nat)
    (guard : SourceStateGuard memory allocator view code native source rank)
    (host : HostState) (hostSource : SourceHostState) (mode : native.mode=.host host)
    (sourceMode : source.mode=.host (.active hostSource))
    (represented : HostStateRepresents native.store.id hostSource host)
    (localInstruction : ∀instruction,host.code[host.pc]?=some instruction →
      match instruction with | .invoke _ _ _ | .publish _ _ _ _=>False | _=>True) :
    tick memory floats allocator select native ⦃out=>∃next nextSource,out=.cont next ∧
      ReentrantCallbacks.Effect view code native.store code next.store ∧
      SourceStateGuard memory allocator view code next nextSource 0 ∧
      Spec.OpenExecution.Transition (sourceModel view (sourcePublication allocator view) select owner stop)
        source [.hostAction] nextSource ∧ sourceHistory next.history=sourceHistory native.history⦄ := by
  obtain ⟨out,actual,next,control,same,stackEq,historyEq,effect,action,controlRep⟩ := WP.spec_imp_exists
    (source_local_tick memory floats allocator allocation view laws code (sourcePublication allocator view) select native
      guard.invariant host mode hostSource represented localInstruction)
  subst out
  rw [actual]
  have nativeSafe := tick_guard memory floats allocator correct allocation view laws select code native guard.native
  rw [actual,WP.spec_ok] at nativeSafe
  obtain ⟨otherCode,otherEffect,afterGuard⟩ := nativeSafe
  let nextSource : Spec.OpenExecution.State SourceControl:=⟨Store.decodeStore view code next.store,.host control,source.stack⟩
  have worldEffect:=local_effect_world effect
  have sameOwner : next.store.id=native.store.id:=effect.metadata.identity
  have representedAfter : SourceControlRepresents next.store.id control next.mode := by
    rw [sameOwner]
    exact controlRep
  have sourceGuard : SourceStateGuard memory allocator view code next nextSource 0 :=
    ⟨effect.invariant,SourceMode.of_control representedAfter afterGuard.2.1,
      by simpa only [nextSource,stackEq] using guard.stack.extend worldEffect,rfl⟩
  have step : Spec.OpenExecution.Transition (sourceModel view (sourcePublication allocator view) select owner stop)
      source [.hostAction] nextSource := by
    rcases source with ⟨s,sourceControl,stack⟩
    dsimp only at sourceMode
    subst sourceControl
    have sameStore : s=Store.decodeStore view code native.store:=guard.storeEq
    subst s
    exact .action action
  exact WP.spec.ret ⟨next,nextSource,rfl,worldEffect,sourceGuard,step,congrArg sourceHistory historyEq⟩
end Exec.Theorems.OpenReentrantControl
