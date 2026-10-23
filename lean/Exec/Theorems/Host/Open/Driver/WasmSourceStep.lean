import Exec.Theorems.Host.Open.Driver.WasmBoundaryArrival
import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Source.State.Observations
import Exec.Spec.Open.ExecutionChosenCounted
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem SourceMode.ok_wasm_source {M A : Type} {memory : runtime.platform.MemoryBuffer M}
    {allocator : runtime.platform.Alloc A} {view : M → Slice U8} {code store native source rank}
    (related : SourceMode memory allocator view code store native source rank)
    (exec : runtime.interp.Execution) (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)
    (same : native=.wasm exec (.Ok ()) root results) :
    ∃f body expected,source=.wasm f body expected := by
  cases related with
  | wasm signature world root results metadata typed => exact ⟨_,_,_,rfl⟩
  | host raw source represented => cases same
  | draft status values owned => cases same
  | preparing exec address signature args results phase metadata ready => cases same
  | finishing exec error root results signature metadata => cases same
  | returned answer sameStore issued => cases same

/-- One actual Wasm dispatch will instantiate this relation with its exact
silent source prefix. It distinguishes continued Wasm from an exposed source
boundary, and keeps the native observation history for either case. -/
inductive WasmSourceStep (choices : SourceOperationChoices) (occurrence : Nat) (select : Selector)
    (owner : Usize) (expected : resulttype) (stack : List (Spec.OpenExecution.Continuation SourceControl))
    (before : config) (beforeHistory : List Observation) :
    Spec.OpenExecution.State SourceControl → List Observation → Prop
  | wasm {count afterConfig afterSource afterHistory}
      (prefixSteps : Spec.ChosenStepsN choices.wasm occurrence count before [] afterConfig)
      (sourceEq : afterSource=⟨afterConfig.1.1,.wasm afterConfig.1.2 afterConfig.2 expected,stack⟩)
      (historyEq : afterHistory=beforeHistory) :
      WasmSourceStep choices occurrence select owner expected stack before beforeHistory afterSource afterHistory
  | arrive {count afterConfig events afterSource afterHistory}
      (prefixSteps : Spec.ChosenStepsN choices.wasm occurrence count before [] afterConfig)
      (arrival : WasmBoundaryArrival select owner expected stack afterConfig events afterSource)
      (historyEq : sourceHistory afterHistory=sourceHistory beforeHistory++visibleSourceHistory events) :
      WasmSourceStep choices occurrence select owner expected stack before beforeHistory afterSource afterHistory

end Exec.Theorems.OpenReentrantControl
