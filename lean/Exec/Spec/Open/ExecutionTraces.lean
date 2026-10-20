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

theorem Trace.trans {H : Type} {model : HostModel H} {n m : Nat}
    {first middle last : State H} {events more : List Observation}
    (head : Trace model n first events middle) (tail : Trace model m middle more last) :
    Trace model (n+m) first (events++more) last := by
  induction head with
  | nil _=>simpa using tail
  | next step rest ih=>
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc] using Trace.next step (ih tail)

/-- Silent atomic-source normalization remains actual Wasm transitions in the
expanded source model; it introduces no host completion event. -/
theorem Trace.wasmSteps {H : Type} (model : HostModel H) {first last : config}
    (steps : StepsH first [] last) (expected : resulttype) (stack : List (Continuation H)) :
    ∃count,Trace model count ⟨first.1.1,.wasm first.1.2 first.2 expected,stack⟩
      (List.replicate count .wasm) ⟨last.1.1,.wasm last.1.2 last.2 expected,stack⟩ := by
  generalize empty : ([] : List HostEvent)=events at steps
  induction steps with
  | refl wf=>exact ⟨0,.nil _⟩
  | @cons first middle last headEvents tailEvents head tail ih=>
    have parts := List.append_eq_nil_iff.mp empty.symm
    rcases parts with ⟨rfl,rfl⟩
    obtain ⟨count,trace⟩ := ih rfl
    rcases first with ⟨⟨s,f⟩,body⟩
    rcases middle with ⟨⟨t,g⟩,after⟩
    exact ⟨count+1,by simpa only [List.replicate_succ,List.singleton_append] using Trace.next (Transition.wasm head) trace⟩

/-- Adding a finite prefix preserves productive source execution. -/
theorem InfiniteTrace.prepend {H : Type} {model : HostModel H} {first next : State H}
    {observed : List Observation} (step : Transition model first observed next)
    (infinite : InfiniteTrace model next) : InfiniteTrace model first := by
  obtain ⟨states,events,initial,steps⟩ := infinite
  refine ⟨(fun n=>match n with | 0=>first | n+1=>states n),
    (fun n=>match n with | 0=>observed | n+1=>events n),rfl,?_⟩
  intro n
  cases n with
  | zero=>simpa only [initial] using step
  | succ n=>exact steps n

theorem Trace.infinite {H : Type} {model : HostModel H} {count : Nat}
    {first last : State H} {events : List Observation} (trace : Trace model count first events last)
    (infinite : InfiniteTrace model last) : InfiniteTrace model first := by
  induction trace with
  | nil _=>exact infinite
  | next step tail ih=>exact InfiniteTrace.prepend step (ih infinite)
end Exec.Spec.OpenExecution
