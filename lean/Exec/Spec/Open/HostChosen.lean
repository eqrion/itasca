import Exec.Spec.Open.ExecutionTraces
import Exec.Spec.HostGrowthSelection
import Exec.Spec.Open.Host
import Exec.Spec.Choices.ChosenContext
import Exec.Spec.Choices.Determinism
namespace Exec.Spec.OpenHost
open SpecExt

theorem Context.chosen_step {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence before after events} (context : Context)
    (step : ChoiceStep choices occurrence before events after) :
    ChoiceStep choices occurrence (context.plug before) events (context.plug after) := by
  induction context with
  | hole=>exact step
  | label arity cont wf inner ih=>exact choice_step_label admissible ih arity cont wf
  | frame arity outer wf inner ih=>exact choice_step_frame admissible ih arity outer wf
  | instructions values tail valuesWf tailWf inner ih=>exact choice_step_instrs admissible ih values tail valuesWf tailWf

/-- Atomic compression of an open interaction retains a preselected source
reply policy. This consumes one host choice at the completed outer call. -/
theorem Pending.compress_chosen {choices : SourceChoices} (admissible : choices.Admissible)
    (occurrence : Nat) (pending : Pending) (typed : Store_ok pending.before) (reply : HostReply)
    (selected : choices.host occurrence pending.before pending.address pending.identity pending.params pending.results pending.arguments=reply) :
    ChoiceStep choices occurrence pending.initial [.call pending.address pending.arguments reply.result] (pending.completed reply) := by
  have inner:=ChoiceStep.host (choices:=choices) (occurrence:=occurrence) pending.before pending.ambient pending.address pending.identity
    pending.params pending.results pending.arguments typed pending.ambientWf pending.host pending.argumentsTyped
  rw [selected] at inner
  exact pending.context.chosen_step admissible inner

/-- A pending host redex is not trap cleanup, including under arbitrary saved
labels, frames and instruction contexts. -/
theorem Pending.initial_nonactive (pending : Pending) (typed : Store_ok pending.before) :
    activeTrap (trapCode pending.initial)=false := by
  have wf : wf_store pending.before:=by cases typed;assumption
  have permitted : (HostReply.mk pending.before none).Admissible pending.before pending.results:=
    ⟨extend_store_refl _ wf,typed,by intro values impossible;cases impossible⟩
  have step:=pending.compress _ permitted
  cases active : activeTrap (trapCode pending.initial) with
  | false=>rfl
  | true=>have empty:=(stepH_active_trap step active).1;cases empty
/-- The same pending source redex determines its host request, even when its
saved evaluation contexts have different administrative representations. -/
theorem Pending.request_unique (left right : Pending) (typed : Store_ok left.before)
    (same : left.initial=right.initial) :
    left.before=right.before ∧ left.address=right.address ∧ left.identity=right.identity ∧
      left.params=right.params ∧ left.results=right.results ∧ left.arguments=right.arguments := by
  have stores : left.before=right.before:=by
    rw [←OpenExecution.pending_store left,←OpenExecution.pending_store right]
    exact congrArg (fun c : config=>c.1.1) same
  have typedRight : Store_ok right.before:=by rw [←stores];exact typed
  have first:=left.compress_chosen defaultSourceChoices_admissible 0 typed ⟨left.before,none⟩ rfl
  have second:=right.compress_chosen defaultSourceChoices_admissible 0 typedRight ⟨right.before,none⟩ rfl
  rw [←same] at second
  have events:=(choice_step_nonactive_deterministic defaultSourceChoices_admissible first second (left.initial_nonactive typed)).1
  simp only [List.cons.injEq,HostEvent.call.injEq] at events
  have addresses:=events.1.1
  have arguments:=events.1.2.1
  obtain ⟨leftModule,leftAt⟩:=left.host
  obtain ⟨rightModule,rightAt⟩:=right.host
  rw [←stores,←addresses] at rightAt
  have functionEq:=Option.some.inj (leftAt.symm.trans rightAt)
  have typesEq:=congrArg funcinst.TYPE functionEq
  have identityEq:=congrArg funcinst.CODE functionEq
  simp only [functype.mk_functype.injEq,list.mk_list.injEq] at typesEq
  simp only [funccode.HOST.injEq] at identityEq
  exact ⟨stores,addresses,identityEq,typesEq.1,typesEq.2,arguments⟩

/-- Any admissible future checked reply resumes the same complete source
configuration. Context representation is not an observable source choice. -/
theorem Pending.completed_unique (left right : Pending) (typed : Store_ok left.before)
    (same : left.initial=right.initial) (reply : HostReply)
    (permitted : reply.Admissible left.before left.results) : left.completed reply=right.completed reply := by
  obtain ⟨stores,addresses,identities,params,results,arguments⟩:=left.request_unique right typed same
  obtain ⟨host,hostAdmissible,selected⟩:=host_reply_selectable 0
    ⟨left.before,left.address,left.identity,left.params,left.results,left.arguments⟩ reply permitted
  let choices : SourceChoices:={defaultSourceChoices with host:=host}
  have admissible : choices.Admissible:=⟨hostAdmissible,defaultSourceChoices_admissible.numeric,
    defaultSourceChoices_admissible.vector,defaultSourceChoices_admissible.memory,defaultSourceChoices_admissible.table⟩
  have typedRight : Store_ok right.before:=by rw [←stores];exact typed
  have selectedRight : choices.host 0 right.before right.address right.identity right.params right.results right.arguments=reply:=by
    rw [←stores,←addresses,←identities,←params,←results,←arguments]
    exact selected
  have first:=left.compress_chosen admissible 0 typed reply selected
  have second:=right.compress_chosen admissible 0 typedRight reply selectedRight
  rw [←same] at second
  exact (choice_step_nonactive_deterministic admissible first second (left.initial_nonactive typed)).2
end Exec.Spec.OpenHost
