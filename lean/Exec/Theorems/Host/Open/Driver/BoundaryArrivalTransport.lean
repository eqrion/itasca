import Exec.Theorems.Host.Open.Driver.WasmBoundaryArrival
import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Source.State.ContextTransport
import Exec.Spec.ValueInstructionsInjective
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem SourceStack.retarget_top {M : Type} {memory : runtime.platform.MemoryBuffer M} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M} {native : List Continuation}
    {tail : List (Spec.OpenExecution.Continuation SourceControl)} {left right : Spec.OpenExecution.Suspension}
    (held : SourceStack memory view code store native (.wasm left::tail))
    (expectedEq : left.expected=right.expected) (same : left.pending.initial=right.pending.initial) :
    SourceStack memory view code store native (.wasm right::tail) := by
  cases held with
  | cons head rest =>
    cases head with
    | wasm exec address base root results suspended saved =>
      exact .cons (.wasm exec address base root results right (saved.retarget expectedEq same)) rest

/-- Every selected step at a quiet Wasm boundary is its values, trap or fresh
host-entry transition. It cannot silently pass a pending host request. -/
theorem boundary_transition_arrival {M : Type} (view : M → Slice U8) (publication : SourcePublication)
    {select owner expected stack configuration events after}
    (choices : SourceOperationChoices) (admissible : choices.wasm.Admissible) (occurrence : Nat)
    (boundary : Spec.OpenHost.QuietBoundary configuration)
    (stop : Spec.OpenExecution.StopReason → config → Prop)
    (step : Spec.OpenExecution.ChoiceTransition (sourceModel view publication select owner stop) (sourceControlChoices choices) occurrence
      ⟨configuration.1.1,.wasm configuration.1.2 configuration.2 expected,stack⟩ events after) :
    WasmBoundaryArrival select owner expected stack configuration events after := by
  rcases configuration with ⟨⟨s,f⟩,body⟩
  cases step with
  | wasm source => exact False.elim (boundary.no_step admissible occurrence source)
  | enter suspended same atStore expectedEq =>
    have arrival:=WasmBoundaryArrival.host (select:=select) (owner:=owner) (expected:=expected) (stack:=stack) suspended expectedEq
    simpa only [same,atStore,sourceModel] using arrival
  | values => exact .values _ _ _
  | trap => exact .trap _ _

private theorem pending_not_terminal (pending : Spec.OpenHost.Pending) (typed : Store_ok pending.before)
    (terminal : Spec.SourceTerminal pending.initial) : False := by
  have host:=pending.compress_chosen Spec.defaultSourceChoices_admissible 0 typed ⟨pending.before,none⟩ rfl
  exact terminal.no_step _ _ (host.erases Spec.defaultSourceChoices_admissible)

/-- Equivalent boundary representations preserve the same native caller and
source outcome. Suspended contexts are retargeted through their proved future
resumption property, without choosing a different callback interaction. -/
theorem WasmBoundaryArrival.transport_guard {M A : Type} {memory : runtime.platform.MemoryBuffer M}
    {allocator : runtime.platform.Alloc A} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {native : State M} {rank : Nat} {select owner expected stack leftCfg rightCfg leftEvents rightEvents leftSource rightSource}
    (left : WasmBoundaryArrival select owner expected stack leftCfg leftEvents leftSource)
    (right : WasmBoundaryArrival select owner expected stack rightCfg rightEvents rightSource)
    (same : leftCfg=rightCfg)
    (guard : SourceStateGuard memory allocator view code native leftSource rank) :
    leftEvents=rightEvents ∧ SourceStateGuard memory allocator view code native rightSource rank := by
  cases left with
  | values s f values =>
    cases right with
    | values t g more =>
      have stores : s=t:=congrArg (fun c : config=>c.1.1) same
      have valuesEq : values=more:=Spec.vals_injective (congrArg (fun c : config=>c.2) same)
      cases stores
      cases valuesEq
      exact ⟨rfl,guard⟩
    | trap t g =>
      have impossible:=congrArg (fun c : config=>Spec.activeTrap (Spec.trapCode c)) same
      simp [Spec.trapCode,Spec.activeTrap_values,Spec.activeTrap] at impossible
    | host suspended expectedEq =>
      have stores : s=suspended.pending.before := by
        simpa only [Spec.OpenExecution.pending_store] using congrArg (fun c : config=>c.1.1) same
      have typed : Store_ok suspended.pending.before := by rw [←stores];exact guard.typed.1
      have terminal : Spec.SourceTerminal suspended.pending.initial := by rw [←same];exact .values _ _
      exact False.elim (pending_not_terminal suspended.pending typed terminal)
  | trap s f =>
    cases right with
    | trap t g =>
      have stores : s=t:=congrArg (fun c : config=>c.1.1) same
      cases stores
      exact ⟨rfl,guard⟩
    | values t g values =>
      have impossible:=congrArg (fun c : config=>Spec.activeTrap (Spec.trapCode c)) same
      simp [Spec.trapCode,Spec.activeTrap_values,Spec.activeTrap] at impossible
    | host suspended expectedEq =>
      have stores : s=suspended.pending.before := by
        simpa only [Spec.OpenExecution.pending_store] using congrArg (fun c : config=>c.1.1) same
      have typed : Store_ok suspended.pending.before := by rw [←stores];exact guard.typed.1
      have terminal : Spec.SourceTerminal suspended.pending.initial := by rw [←same];exact .trap _
      exact False.elim (pending_not_terminal suspended.pending typed terminal)
  | host suspended expectedEq =>
    cases right with
    | values t g values =>
      have terminal : Spec.SourceTerminal suspended.pending.initial := by rw [same];exact .values _ _
      exact False.elim (pending_not_terminal suspended.pending guard.typed.1 terminal)
    | trap t g =>
      have terminal : Spec.SourceTerminal suspended.pending.initial := by rw [same];exact .trap _
      exact False.elim (pending_not_terminal suspended.pending guard.typed.1 terminal)
    | host other otherExpected =>
      obtain ⟨stores,addresses,identities,params,results,arguments⟩:=suspended.pending.request_unique other.pending guard.typed.1 same
      have represented : SourceMode memory allocator view code native.store native.mode
          (.host (.active (sourceHostEntry select owner other.pending.identity other.pending.arguments))) rank := by
        rw [←identities,←arguments]
        exact guard.mode
      have saved:=guard.stack.retarget_top (expectedEq.trans otherExpected.symm) same
      exact ⟨by rw [addresses,identities,arguments],
        ⟨guard.invariant,represented,saved,stores.symm.trans guard.storeEq⟩⟩
end Exec.Theorems.OpenReentrantControl
