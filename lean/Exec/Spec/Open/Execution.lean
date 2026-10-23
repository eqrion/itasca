import Exec.Spec.Open.Host
import Exec.Spec.Typing.InvocationTyping
import Exec.Spec.StepStoreExtension

/-! Expanded source execution separates host control, nested invocation and
Wasm steps. Host effects and replies are independent source relations. -/
namespace Exec.Spec.OpenExecution
open SpecExt

/-- API interruption and resource exhaustion stop at a source prefix. They
are separate outcomes from a Wasm trap or a diverging computation. -/
inductive StopReason where
  | allocation
  | frames
  | values
  | interrupt

inductive InvocationResult where
  | returned (values : List val)
  | trapped
  | rejected
  | stopped (reason : StopReason)

/-- Host control exposes immutable requests and checked effects. Local actions
must respect source store permissions; no control termination is required. -/
structure HostModel (H : Type) where
  enter : Nat → List val → H
  action : store → H → store → H → Prop
  action_preserves : ∀s h t k,action s h t k → Store_ok s → Extend_store s t ∧ Store_ok t
  invoke : H → funcaddr → List val → H → Prop
  finish : store → H → Option (List val) → Prop
  resume : H → InvocationResult → H
  /-- Independent permission for stopping at this source prefix. Native
  refinement must justify it from the selected resource/interrupt policy. -/
  permitsStop : StopReason → config → Prop

inductive Mode (H : Type) where
  | wasm (ambient : frame) (body : List admininstr) (expected : resulttype)
  | host (control : H)
  | hostReturn (result : Option (List val))
  | invokeRequest (address : funcaddr) (args : List val) (params results : List valtype)
  | invokeReturn (result : InvocationResult)
  | completed (result : InvocationResult)

structure Suspension where
  pending : OpenHost.Pending
  expected : resulttype
  typed : Config_ok pending.initial expected

inductive Continuation (H : Type) where
  | wasm (suspension : Suspension)
  | host (control : H)

structure State (H : Type) where
  store : _root_.store
  mode : Mode H
  stack : List (Continuation H)

inductive Observation where
  | wasm
  | hostEnter (address : funcaddr) (identity : Nat) (args : List val)
  | hostAction
  | hostExit (result : Option (List val))
  | invokeEnter (address : funcaddr) (args : List val)
  | invokeExit (result : InvocationResult)
  | completedHost (event : HostEvent)

/-- Every suspended Wasm call retains its original request while the shared
store grows through host actions and arbitrarily nested executions. -/
def StackTyped {H : Type} (current : store) : List (Continuation H) → Prop
  | [] => True
  | .host _::tail => StackTyped current tail
  | .wasm suspended::tail => Extend_store suspended.pending.before current ∧ StackTyped current tail

def ModeTyped {H : Type} (current : store) : Mode H → Prop
  | .wasm ambient body expected => Config_ok ⟨⟨current,ambient⟩,body⟩ expected
  | .invokeRequest address _ params results => address<current.FUNCS.length ∧
      current.FUNCS[address]!.TYPE=.mk_functype (.mk_list params) (.mk_list results)
  | _ => True

def State.Typed {H : Type} (state : State H) : Prop :=
  Store_ok state.store ∧ ModeTyped state.store state.mode ∧ StackTyped state.store state.stack

private theorem typed_store_wf {s : store} (typed : Store_ok s) : wf_store s := by
  cases typed
  assumption

theorem StackTyped.extend {H : Type} {before after : store} {stack : List (Continuation H)}
    (held : StackTyped before stack) (extension : Extend_store before after) : StackTyped after stack := by
  induction stack with
  | nil => trivial
  | cons head tail ih =>
    cases head with
    | host control => exact ih held
    | wasm suspended => exact ⟨extend_store_trans held.1 extension,ih held.2⟩

/-- Source transitions never invoke an atomic native host callback. A host
entry suspends the exact source context; a completed reply resumes it through
the separately proved atomic compression rule. -/
inductive Transition {H : Type} (model : HostModel H) : State H → List Observation → State H → Prop
  | wasm {s t f g before after expected stack}
      (source : StepH ⟨⟨s,f⟩,before⟩ [] ⟨⟨t,g⟩,after⟩) :
      Transition model ⟨s,.wasm f before expected,stack⟩ [.wasm] ⟨t,.wasm g after expected,stack⟩
  | enter {s f body expected stack} (suspended : Suspension)
      (same : suspended.pending.initial=⟨⟨s,f⟩,body⟩)
      (atStore : suspended.pending.before=s) (expectedEq : suspended.expected=expected) :
      Transition model ⟨s,.wasm f body expected,stack⟩
        [.hostEnter suspended.pending.address suspended.pending.identity suspended.pending.arguments]
        ⟨s,.host (model.enter suspended.pending.identity suspended.pending.arguments),.wasm suspended::stack⟩
  | action {s t control next stack} (effect : model.action s control t next) :
      Transition model ⟨s,.host control,stack⟩ [.hostAction] ⟨t,.host next,stack⟩
  | requestInvoke {s control address args next stack params results}
      (request : model.invoke control address args next)
      (bound : address<s.FUNCS.length)
      (signature : s.FUNCS[address]!.TYPE=.mk_functype (.mk_list params) (.mk_list results)) :
      Transition model ⟨s,.host control,stack⟩ [.invokeEnter address args]
        ⟨s,.invokeRequest address args params results,.host next::stack⟩
  | acceptInvoke {s address args params results stack}
      (arguments : ResultsTyped s params args) :
      Transition model ⟨s,.invokeRequest address args params results,stack⟩ []
        ⟨s,.wasm invocationFrame (vals args++[.CALL_ADDR address]) (.mk_list results),stack⟩
  | rejectInvoke {s address args params results stack}
      (rejected : ¬ResultsTyped s params args) :
      Transition model ⟨s,.invokeRequest address args params results,stack⟩ []
        ⟨s,.invokeReturn .rejected,stack⟩
  | cutoff {s f body expected stack reason}
      (permitted : model.permitsStop reason ⟨⟨s,f⟩,body⟩) :
      Transition model ⟨s,.wasm f body expected,stack⟩ []
        ⟨s,.invokeReturn (.stopped reason),stack⟩
  | finish {s control result stack} (finished : model.finish s control result) :
      Transition model ⟨s,.host control,stack⟩ [.hostExit result] ⟨s,.hostReturn result,stack⟩
  | values {s f values expected stack} :
      Transition model ⟨s,.wasm f (vals values) expected,stack⟩ []
        ⟨s,.invokeReturn (.returned values),stack⟩
  | trap {s f expected stack} :
      Transition model ⟨s,.wasm f [.TRAP] expected,stack⟩ [] ⟨s,.invokeReturn .trapped,stack⟩
  | resumeHost {s result control stack} :
      Transition model ⟨s,.invokeReturn result,.host control::stack⟩ [.invokeExit result] ⟨s,.host (model.resume control result),stack⟩
  | completeInvoke {s result} :
      Transition model ⟨s,.invokeReturn result,[]⟩ [.invokeExit result] ⟨s,.completed result,[]⟩
  | resumeWasm {s result suspended stack f body}
      (reply : (HostReply.mk s result).Admissible suspended.pending.before suspended.pending.results)
      (completed : suspended.pending.completed ⟨s,result⟩=⟨⟨s,f⟩,body⟩) :
      Transition model ⟨s,.hostReturn result,.wasm suspended::stack⟩
        [.completedHost (.call suspended.pending.address suspended.pending.arguments result)]
        ⟨s,.wasm f body suspended.expected,stack⟩

  | rejectWasm {s values suspended stack f body}
      (rejected : ¬ResultsTyped s suspended.pending.results values)
      (reply : (HostReply.mk s none).Admissible suspended.pending.before suspended.pending.results)
      (completed : suspended.pending.completed ⟨s,none⟩=⟨⟨s,f⟩,body⟩) :
      Transition model ⟨s,.hostReturn (some values),.wasm suspended::stack⟩
        [.completedHost (.call suspended.pending.address suspended.pending.arguments none)]
        ⟨s,.wasm f body suspended.expected,stack⟩

/-- Store typing and all suspended requests survive each observable source
prefix. This theorem has no callback-normality or bounded-nesting premise. -/
theorem Transition.preserves {H : Type} {model : HostModel H} {before after : State H} {events : List Observation}
    (step : Transition model before events after) (held : before.Typed) :
    after.Typed ∧ Extend_store before.store after.store := by
  cases step with
  | wasm source =>
    have extension := stepH_store_extension source held.2.1
    have typed := stepH_config_preserved source held.2.1
    exact ⟨⟨config_ok_store typed,typed,held.2.2.extend extension⟩,extension⟩
  | enter suspended same atStore expectedEq =>
    have wf := typed_store_wf held.1
    exact ⟨⟨held.1,trivial,by
      change Extend_store suspended.pending.before _ ∧ _
      rw [atStore]
      exact ⟨extend_store_refl _ wf,held.2.2⟩⟩,extend_store_refl _ wf⟩
  | action effect =>
    obtain ⟨extension,fresh⟩ := model.action_preserves _ _ _ _ effect held.1
    exact ⟨⟨fresh,trivial,held.2.2.extend extension⟩,extension⟩
  | requestInvoke request bound signature =>
    have wf := typed_store_wf held.1
    exact ⟨⟨held.1,⟨bound,signature⟩,held.2.2⟩,extend_store_refl _ wf⟩
  | acceptInvoke arguments =>
    have wf := typed_store_wf held.1
    obtain ⟨bound,signature⟩ := held.2.1
    exact ⟨⟨held.1,invocation_config_ok held.1 _ _ _ _ bound signature arguments,held.2.2⟩,extend_store_refl _ wf⟩
  | rejectInvoke rejected =>
    have wf := typed_store_wf held.1
    exact ⟨⟨held.1,trivial,held.2.2⟩,extend_store_refl _ wf⟩
  | cutoff permitted =>
    have wf := typed_store_wf held.1
    exact ⟨⟨held.1,trivial,held.2.2⟩,extend_store_refl _ wf⟩
  | finish finished =>
    have wf := typed_store_wf held.1
    exact ⟨⟨held.1,trivial,held.2.2⟩,extend_store_refl _ wf⟩
  | values | trap =>
    have wf := typed_store_wf held.1
    exact ⟨⟨held.1,trivial,held.2.2⟩,extend_store_refl _ wf⟩
  | resumeHost =>
    have wf := typed_store_wf held.1
    exact ⟨⟨held.1,trivial,held.2.2⟩,extend_store_refl _ wf⟩
  | completeInvoke =>
    have wf := typed_store_wf held.1
    exact ⟨⟨held.1,trivial,trivial⟩,extend_store_refl _ wf⟩
  | @resumeWasm s result suspended stack f body reply completed =>
    have wf := typed_store_wf held.1
    refine ⟨⟨held.1,?_,held.2.2.2⟩,extend_store_refl _ wf⟩
    dsimp only [ModeTyped]
    rw [←completed]
    exact OpenHost.Pending.completed_typed _ _ reply suspended.typed

  | @rejectWasm s values suspended stack f body rejected reply completed =>
    have wf := typed_store_wf held.1
    refine ⟨⟨held.1,?_,held.2.2.2⟩,extend_store_refl _ wf⟩
    dsimp only [ModeTyped]
    rw [←completed]
    exact OpenHost.Pending.completed_typed _ _ reply suspended.typed

end Exec.Spec.OpenExecution
