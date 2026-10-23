import Exec.Theorems.Host.Open.Source.Control.Actions
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp

/-- Invocation observations retain API cutoffs separately from Wasm traps.
The Objects case makes the projection total; checked public invocation excludes
that result independently. -/
def sourceInvocationResult (status : Status) (values : alloc.vec.Vec runtime.Value) : Spec.OpenExecution.InvocationResult :=
  match status with
  | .Ok _=>.returned (values.val.map sourceValue)
  | .Err (.Trap _)=>.trapped
  | .Err (.Exhausted .Allocation)=>.stopped .allocation
  | .Err (.Exhausted .CallStack)=>.stopped .frames
  | .Err (.Exhausted .Values)=>.stopped .values
  | .Err (.Exhausted .Objects)=>.stopped .allocation
  | .Err .Terminated=>.stopped .interrupt
  | .Err _=>.rejected

/-- Source internal reductions are invisible to the expanded native history;
call/return nesting and completed outer host events remain observable. -/
def visibleSourceObservation : Spec.OpenExecution.Observation → List Spec.OpenExecution.Observation
  | .wasm | .hostAction=>[]
  | observed=>[observed]

def visibleSourceHistory (events : List Spec.OpenExecution.Observation) : List Spec.OpenExecution.Observation :=
  events.flatMap visibleSourceObservation

def sourceObservation : Observation → List Spec.OpenExecution.Observation
  | .hostEnter none _ _=>[]
  | .hostEnter (some address) identity args=>[.hostEnter address.index.val identity.val (args.val.map sourceValue)]
  | .hostExit status values=>[.hostExit (sourceReply status values)]
  | .invokeEnter address args=>[.invokeEnter address.index.val (args.val.map sourceValue)]
  | .invokeExit status values=>[.invokeExit (sourceInvocationResult status values)]
  | .completedHost _ events=>events.map Spec.OpenExecution.Observation.completedHost

def sourceHistory (events : List Observation) : List Spec.OpenExecution.Observation :=
  events.flatMap sourceObservation

theorem visibleSourceHistory_append (first next : List Spec.OpenExecution.Observation) :
    visibleSourceHistory (first++next)=visibleSourceHistory first++visibleSourceHistory next := by
  simp only [visibleSourceHistory,List.flatMap_append]

theorem visible_sourceObservation (event : Observation) :
    visibleSourceHistory (sourceObservation event)=sourceObservation event := by
  cases event with
  | hostEnter address identity args=>cases address <;> rfl
  | hostExit status values=>rfl
  | invokeEnter address args=>rfl
  | invokeExit status values=>rfl
  | completedHost depth events=>
    induction events with
    | nil=>rfl
    | cons event rest ih=>
      simpa only [sourceObservation,List.map_cons,visibleSourceHistory,List.flatMap_cons,
        visibleSourceObservation,List.singleton_append] using congrArg (fun xs=>.completedHost event::xs) ih

theorem visible_sourceHistory (events : List Observation) : visibleSourceHistory (sourceHistory events)=sourceHistory events := by
  induction events with
  | nil=>rfl
  | cons event tail ih=>
    simp only [sourceHistory,List.flatMap_cons,visibleSourceHistory_append,visible_sourceObservation]
    exact congrArg (fun xs=>sourceObservation event++xs) ih
/-- Internal Wasm reductions do not change the expanded host/API history. -/
@[simp] theorem visibleSourceHistory_wasm (count : Nat) :
    visibleSourceHistory (List.replicate count .wasm)=[] := by
  simp only [visibleSourceHistory,List.flatMap_replicate,visibleSourceObservation,List.flatten_replicate_nil]

theorem sourceHistory_visible_append {before after : List Observation} {events : List Spec.OpenExecution.Observation}
    (same : sourceHistory after=sourceHistory before++events) :
    sourceHistory after=sourceHistory before++visibleSourceHistory events := by
  simpa only [visibleSourceHistory_append,visible_sourceHistory] using congrArg visibleSourceHistory same

end Exec.Theorems.OpenReentrantControl
