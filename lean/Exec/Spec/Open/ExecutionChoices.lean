import Exec.Spec.Open.ExecutionTraces
import Exec.Spec.Choices.Steps
namespace Exec.Spec.OpenExecution
open SpecExt

/-- Independent choices for primitive Wasm reductions and finite host-local
operations. Request and finish selections inspect source control only; effects
must separately satisfy the model's source operation permissions. -/
structure Choices (H : Type) where
  wasm : SourceChoices
  action : Nat → store → H → Option (store × H)
  invoke : Nat → H → Option (funcaddr × List val × H)
  finish : Nat → store → H → Option (Option (List val))

structure Choices.Admissible {H : Type} (choices : Choices H) (model : HostModel H) : Prop where
  wasm : choices.wasm.Admissible
  action : ∀occurrence s h t k,choices.action occurrence s h=some (t,k) → model.action s h t k
  invoke : ∀occurrence h address args k,choices.invoke occurrence h=some (address,args,k) → model.invoke h address args k
  finish : ∀occurrence s h result,choices.finish occurrence s h=some result → model.finish s h result

/-- Fixed-choice combined execution has no arbitrary API cutoff. Resource
failures remain classified alternatives of native partial soundness; deriving
this selected relation requires independent availability and capacity bounds. -/
inductive ChoiceTransition {H : Type} (model : HostModel H) (choices : Choices H) (occurrence : Nat) :
    State H → List Observation → State H → Prop
  | wasm {s t f g before after expected stack}
      (source : ChoiceStep choices.wasm occurrence ⟨⟨s,f⟩,before⟩ [] ⟨⟨t,g⟩,after⟩) :
      ChoiceTransition model choices occurrence ⟨s,.wasm f before expected,stack⟩ [.wasm] ⟨t,.wasm g after expected,stack⟩
  | enter {s f body expected stack} (suspended : Suspension)
      (same : suspended.pending.initial=⟨⟨s,f⟩,body⟩)
      (atStore : suspended.pending.before=s) (expectedEq : suspended.expected=expected) :
      ChoiceTransition model choices occurrence ⟨s,.wasm f body expected,stack⟩
        [.hostEnter suspended.pending.address suspended.pending.identity suspended.pending.arguments]
        ⟨s,.host (model.enter suspended.pending.identity suspended.pending.arguments),.wasm suspended::stack⟩
  | action {s t control next stack} (selected : choices.action occurrence s control=some (t,next)) :
      ChoiceTransition model choices occurrence ⟨s,.host control,stack⟩ [.hostAction] ⟨t,.host next,stack⟩
  | requestInvoke {s control address args next stack params results}
      (selected : choices.invoke occurrence control=some (address,args,next))
      (bound : address<s.FUNCS.length)
      (signature : s.FUNCS[address]!.TYPE=.mk_functype (.mk_list params) (.mk_list results)) :
      ChoiceTransition model choices occurrence ⟨s,.host control,stack⟩ [.invokeEnter address args]
        ⟨s,.invokeRequest address args params results,.host next::stack⟩
  | acceptInvoke {s address args params results stack} (arguments : ResultsTyped s params args) :
      ChoiceTransition model choices occurrence ⟨s,.invokeRequest address args params results,stack⟩ []
        ⟨s,.wasm invocationFrame (vals args++[.CALL_ADDR address]) (.mk_list results),stack⟩
  | rejectInvoke {s address args params results stack} (rejected : ¬ResultsTyped s params args) :
      ChoiceTransition model choices occurrence ⟨s,.invokeRequest address args params results,stack⟩ []
        ⟨s,.invokeReturn .rejected,stack⟩
  | finish {s control result stack} (selected : choices.finish occurrence s control=some result) :
      ChoiceTransition model choices occurrence ⟨s,.host control,stack⟩ [.hostExit result] ⟨s,.hostReturn result,stack⟩
  | values {s f values expected stack} :
      ChoiceTransition model choices occurrence ⟨s,.wasm f (vals values) expected,stack⟩ []
        ⟨s,.invokeReturn (.returned values),stack⟩
  | trap {s f expected stack} :
      ChoiceTransition model choices occurrence ⟨s,.wasm f [.TRAP] expected,stack⟩ [] ⟨s,.invokeReturn .trapped,stack⟩
  | resumeHost {s result control stack} :
      ChoiceTransition model choices occurrence ⟨s,.invokeReturn result,.host control::stack⟩ [.invokeExit result]
        ⟨s,.host (model.resume control result),stack⟩
  | completeInvoke {s result} :
      ChoiceTransition model choices occurrence ⟨s,.invokeReturn result,[]⟩ [.invokeExit result] ⟨s,.completed result,[]⟩
  | resumeWasm {s result suspended stack f body}
      (reply : (HostReply.mk s result).Admissible suspended.pending.before suspended.pending.results)
      (completed : suspended.pending.completed ⟨s,result⟩=⟨⟨s,f⟩,body⟩) :
      ChoiceTransition model choices occurrence ⟨s,.hostReturn result,.wasm suspended::stack⟩
        [.completedHost (.call suspended.pending.address suspended.pending.arguments result)]
        ⟨s,.wasm f body suspended.expected,stack⟩
  | rejectWasm {s values suspended stack f body}
      (rejected : ¬ResultsTyped s suspended.pending.results values)
      (reply : (HostReply.mk s none).Admissible suspended.pending.before suspended.pending.results)
      (completed : suspended.pending.completed ⟨s,none⟩=⟨⟨s,f⟩,body⟩) :
      ChoiceTransition model choices occurrence ⟨s,.hostReturn (some values),.wasm suspended::stack⟩
        [.completedHost (.call suspended.pending.address suspended.pending.arguments none)]
        ⟨s,.wasm f body suspended.expected,stack⟩

theorem ChoiceTransition.erases {H : Type} {model : HostModel H} {choices : Choices H}
    (admissible : choices.Admissible model) {occurrence first events last}
    (step : ChoiceTransition model choices occurrence first events last) : Transition model first events last := by
  cases step with
  | wasm source=>exact .wasm (source.erases admissible.wasm)
  | action selected=>exact .action (admissible.action _ _ _ _ _ selected)
  | requestInvoke selected bound signature=>exact .requestInvoke (admissible.invoke _ _ _ _ _ selected) bound signature
  | finish selected=>exact .finish (admissible.finish _ _ _ _ selected)
  | enter suspended same atStore expectedEq=>exact .enter suspended same atStore expectedEq
  | acceptInvoke arguments=>exact .acceptInvoke arguments
  | rejectInvoke rejected=>exact .rejectInvoke rejected
  | values=>exact .values
  | trap=>exact .trap
  | resumeHost=>exact .resumeHost
  | completeInvoke=>exact .completeInvoke
  | resumeWasm reply completed=>exact .resumeWasm reply completed
  | rejectWasm rejected reply completed=>exact .rejectWasm rejected reply completed

inductive ChoiceTrace {H : Type} (model : HostModel H) (choices : Choices H) :
    Nat → Nat → State H → List Observation → State H → Prop
  | nil (occurrence state) : ChoiceTrace model choices occurrence 0 state [] state
  | next {occurrence count first middle last events more}
      (step : ChoiceTransition model choices occurrence first events middle)
      (tail : ChoiceTrace model choices (occurrence+1) count middle more last) :
      ChoiceTrace model choices occurrence (count+1) first (events++more) last

theorem ChoiceTrace.erases {H : Type} {model : HostModel H} {choices : Choices H}
    (admissible : choices.Admissible model) {occurrence count first events last}
    (trace : ChoiceTrace model choices occurrence count first events last) : Trace model count first events last := by
  induction trace with
  | nil _ _=>exact .nil _
  | next step tail ih=>exact .next (step.erases admissible) ih

def ChoiceInfinite {H : Type} (model : HostModel H) (choices : Choices H) (occurrence : Nat) (first : State H) : Prop:=
  ∃states : Nat → State H,∃events : Nat → List Observation,states 0=first ∧
    ∀n,ChoiceTransition model choices (occurrence+n) (states n) (events n) (states (n+1))

theorem ChoiceInfinite.erases {H : Type} {model : HostModel H} {choices : Choices H}
    (admissible : choices.Admissible model) {occurrence first}
    (infinite : ChoiceInfinite model choices occurrence first) : InfiniteTrace model first := by
  obtain ⟨states,events,initial,steps⟩:=infinite
  exact ⟨states,events,initial,fun n=>(steps n).erases admissible⟩
end Exec.Spec.OpenExecution
