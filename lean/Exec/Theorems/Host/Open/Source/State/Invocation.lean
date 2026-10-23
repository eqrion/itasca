import Exec.Theorems.Host.Open.Source.State.Finite
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
import Exec.Theorems.Host.Open.Driver.DriverPrefixes
import Exec.Theorems.Host.Open.Source.State.RootGuard
import Exec.Theorems.Host.Open.Erasure.InvocationEquivalence
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

def sourceInvocationEntry {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (address : runtime.FuncAddr) (signature : Itasca.types.FuncType)
    (args : Slice runtime.Value) : Spec.OpenExecution.State SourceControl:=
  ⟨Store.decodeStore view code store,.invokeRequest address.index.val (args.val.map sourceValue)
    (signature.params.val.map sourceType) (signature.results.val.map sourceType),[]⟩

end Exec.Theorems.OpenReentrantControl
