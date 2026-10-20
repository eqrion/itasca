import Exec.Spec.HostCall

/-! Independent choices for completed atomic host interactions. These choices
are specified using source typing and extension, without an interpreter result.
The open model must additionally represent interactions that do not complete. -/
namespace Exec.Spec
open SpecExt

/-- A reply includes committed effects on return and trap. -/
structure HostReply where
  after : store
  result : Option (List val)

/-- The source conditions on an atomic host reply. Result typing is needed
only for a normal reply; both alternatives retain source store typing. -/
def HostReply.Admissible (before : store) (results : List valtype) (reply : HostReply) : Prop :=
  Extend_store before reply.after ∧ Store_ok reply.after ∧
    ∀ values, reply.result = some values → ResultsTyped reply.after results values

/-- A choice can depend on the complete independent source request and its
occurrence, so repeated calls may observe changing external host state. -/
abbrev HostChoices := Nat → store → funcaddr → Nat → List valtype → List valtype → List val → HostReply

/-- Source admissibility is conditional on a typed host redex, rather than
on the existence of a corresponding concrete callback result. -/
def HostChoices.Admissible (choices : HostChoices) : Prop :=
  ∀ occurrence before address identity params results args,
    Store_ok before → HostFunction before address identity params results →
    ResultsTyped before params args →
    (choices occurrence before address identity params results args).Admissible before results

/-- The output configuration determined by the selected reply. -/
def HostReply.configuration (reply : HostReply) (ambient : frame) : config :=
  ⟨⟨reply.after,ambient⟩,match reply.result with | some values => vals values | none => [.TRAP]⟩

/-- Consuming an admissible selected reply erases to the strengthened source
host rule, preserving its final store and outer event. -/
theorem host_choice_erases (choices : HostChoices) (admissible : choices.Admissible)
    (occurrence : Nat) (before : store) (ambient : frame) (address : funcaddr) (identity : Nat)
    (params results : List valtype) (args : List val)
    (typedStore : Store_ok before) (typedFrame : wf_frame ambient)
    (host : HostFunction before address identity params results)
    (arguments : ResultsTyped before params args) :
    let reply := choices occurrence before address identity params results args
    StepH ⟨⟨before,ambient⟩,vals args ++ [.CALL_ADDR address]⟩
      [.call address args reply.result] (reply.configuration ambient) := by
  dsimp only
  obtain ⟨extension,typed,returned⟩ := admissible occurrence before address identity params results args typedStore host arguments
  generalize selected : choices occurrence before address identity params results args = reply at extension typed returned ⊢
  cases reply with
  | mk after result =>
    cases result with
    | none => exact host_trap_step host arguments extension typed typedFrame
    | some values => exact host_return_step host arguments extension typed (returned values rfl) typedFrame

/-- Once the reply is fixed, its output store, values or trap, and event are
fixed. This is local determinism, not determinism of arbitrary source runs. -/
theorem host_choice_deterministic {choices : HostChoices} {occurrence : Nat} {before : store}
    {address : funcaddr} {identity : Nat} {params results : List valtype} {args : List val}
    {first second : HostReply}
    (left : choices occurrence before address identity params results args = first)
    (right : choices occurrence before address identity params results args = second) : first = second :=
  left.symm.trans right

/-- A trapping callback without effects is an inhabited source policy for
every typed host request. Arbitrary native callbacks still need refinement. -/
def trappingHostChoice : HostChoices := fun _ before _ _ _ _ _ => ⟨before,none⟩

theorem trappingHostChoice_admissible : trappingHostChoice.Admissible := by
  intro occurrence before address identity params results args typed _ _
  have storeWf : wf_store before := by cases typed; assumption
  exact ⟨extend_store_refl before storeWf,typed,by intro values impossible; cases impossible⟩

end Exec.Spec
