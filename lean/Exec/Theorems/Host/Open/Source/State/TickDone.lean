import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Source.Control.Publication
import Exec.Spec.Open.ExecutionTraces
import Exec.Theorems.Host.Open.Source.Control.LocalStep
import Exec.Theorems.Host.Open.Source.Control.Actions
import Exec.Theorems.Host.Open.Driver.DriverTick
import Exec.Theorems.Host.Open.Source.Wasm.InvokeStep
import Exec.Theorems.Host.Open.Source.State.MissingStep
import Exec.Theorems.Host.Open.Driver.CompletedEvents
import Exec.Theorems.Host.Reentrant.FiniteReentrantCallbacks
import Exec.Theorems.Host.Open.Source.State.Observations
import Exec.Spec.Open.ExecutionCounted
import Exec.Interp.Relations.EventfulControl
import Exec.Theorems.Host.Open.Source.State.ActiveTick
import Exec.Theorems.Host.Open.Source.State.World
import Exec.Interp.Host.OpenStoppedLoop
import Exec.Theorems.Host.Open.Source.State.SavedResumption
import Exec.Theorems.Host.Open.Driver.CheckedSourceReply
import Exec.Spec.Open.ExecutionReplies
import Exec.Abs.Sim.OpenContextTrap
import Exec.Interp.Host.HostResumeStatus
import Exec.Theorems.Host.Open.Source.Wasm.Preparing
import Exec.Theorems.Host.Open.Source.State.ErrorFinish
import Exec.Theorems.Host.Open.Source.Wasm.InvokeReturn
import Exec.Theorems.Host.Open.Source.Wasm.InvokeExit
import Exec.Theorems.Host.Open.Driver.DriverStackSafety
import Exec.Theorems.Host.Open.Driver.ReentrantStack
import Exec.Theorems.Host.Open.Driver.ReentrantHistory
import Exec.Theorems.Host.Open.Erasure.EraseShape
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- The public root has one source completion boundary. Nested task returns
cannot be mistaken for completion of the root invocation. -/
def SourceOutcome {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (outcome : Outcome M) (source : Spec.OpenExecution.State SourceControl) : Prop:=
  match outcome with
  | .host _ _=>False
  | .invocation answer _=>source.mode=.completed (sourceInvocationResult answer.1 answer.2.2.2.2) ∧
      source.stack=[] ∧ source.store=Store.decodeStore view code answer.2.2.1

end Exec.Theorems.OpenReentrantControl
