import Exec.Spec.Choices.HostChoices
import Exec.Spec.Typing.HostStepPreservation

/-! Source-only suspended host interactions. Contexts are generated evaluation
contexts; a returned reply compresses to the original atomic source rule. -/
namespace Exec.Spec.OpenHost
open SpecExt

inductive Context where
  | hole
  | label (arity : Nat) (continuation : List instr) (wellFormed : Forall wf_instr continuation) (inner : Context)
  | frame (arity : Nat) (outer : _root_.frame) (wellFormed : wf_frame outer) (inner : Context)
  | instructions (values : List val) (after : List admininstr)
      (valuesWf : Forall wf_val values) (afterWf : Forall wf_admininstr after) (inner : Context)

def Context.plug : Context → config → config
  | .hole,c => c
  | .label arity cont _ inner,c => labelContext arity cont (inner.plug c)
  | .frame arity outer _ inner,c => frameContext arity outer (inner.plug c)
  | .instructions values after _ _ inner,c => instrContext values after (inner.plug c)

theorem Context.step {before after : config} {events : List HostEvent}
    (context : Context) (source : StepH before events after) :
    StepH (context.plug before) events (context.plug after) := by
  induction context with
  | hole => exact source
  | label arity cont wf inner ih => exact stepH_label ih arity cont wf
  | frame arity outer wf inner ih => exact stepH_frame ih arity outer wf
  | instructions values after valuesWf afterWf inner ih => exact stepH_instrs ih values after valuesWf afterWf

/-- The independent source request captured when control enters a host. Its
original store and redex remain fixed while host-local and nested tasks run. -/
structure Pending where
  before : store
  ambient : _root_.frame
  context : Context
  address : funcaddr
  identity : Nat
  params : List valtype
  results : List valtype
  arguments : List val
  host : HostFunction before address identity params results
  argumentsTyped : ResultsTyped before params arguments
  ambientWf : wf_frame ambient

def Pending.initial (pending : Pending) : config :=
  pending.context.plug ⟨⟨pending.before,pending.ambient⟩,vals pending.arguments++[.CALL_ADDR pending.address]⟩

def Pending.completed (pending : Pending) (reply : HostReply) : config :=
  pending.context.plug (reply.configuration pending.ambient)

/-- Conservativity retains the same returned store and outer event, regardless
of the finite nested history used to obtain an admissible reply. -/
theorem Pending.compress (pending : Pending) (reply : HostReply)
    (admissible : reply.Admissible pending.before pending.results) :
    StepH pending.initial [.call pending.address pending.arguments reply.result] (pending.completed reply) := by
  obtain ⟨extension,storeTyped,returned⟩ := admissible
  apply pending.context.step
  cases reply with
  | mk after result =>
    cases result with
    | none => exact host_trap_step pending.host pending.argumentsTyped extension storeTyped pending.ambientWf
    | some values =>
      exact host_return_step pending.host pending.argumentsTyped extension storeTyped (returned values rfl) pending.ambientWf

/-- Compressing a completed interaction also preserves the typing of the
entire suspended configuration, including enclosing labels and frames. -/
theorem Pending.completed_typed (pending : Pending) (reply : HostReply)
    (admissible : reply.Admissible pending.before pending.results)
    {expected : resulttype} (typed : Config_ok pending.initial expected) :
    Config_ok (pending.completed reply) expected := stepH_config_preserved (pending.compress reply admissible) typed
end Exec.Spec.OpenHost
