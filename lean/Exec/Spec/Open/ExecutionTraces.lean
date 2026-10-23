import Exec.Spec.Open.Execution
namespace Exec.Spec.OpenExecution
open SpecExt

theorem context_store (context : OpenHost.Context) (configuration : config) :
    (context.plug configuration).1.1=configuration.1.1 := by
  induction context with
  | hole=>rfl
  | label arity continuation wf inner ih=>
    simpa only [OpenHost.Context.plug,labelContext] using ih
  | frame arity outer wf inner ih=>
    simpa only [OpenHost.Context.plug,frameContext] using ih
  | instructions values after valuesWf afterWf inner ih=>
    simpa only [OpenHost.Context.plug,instrContext] using ih

theorem pending_store (pending : OpenHost.Pending) : pending.initial.1.1=pending.before :=
  context_store pending.context _

end Exec.Spec.OpenExecution
