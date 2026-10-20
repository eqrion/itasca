import Exec.Spec.Choices.Selection
import Exec.Spec.Choices.HostChoices
import Exec.Spec.Choices.GrowthChoices

/-! Every independently admissible host or growth reply is selectable by an
admissible source policy, without reference to an interpreter result. -/

namespace Exec.Spec
open SpecExt

structure HostRequest where
  before : store
  address : funcaddr
  identity : Nat
  params : List valtype
  results : List valtype
  args : List val

theorem host_reply_selectable (occurrence : Nat) (request : HostRequest) (reply : HostReply)
    (permitted : reply.Admissible request.before request.results) :
    ∃ choices : HostChoices, choices.Admissible ∧
      choices occurrence request.before request.address request.identity request.params request.results request.args = reply := by
  let allowed (key : HostRequest) (answer : HostReply) : Prop :=
    Store_ok key.before → HostFunction key.before key.address key.identity key.params key.results →
      ResultsTyped key.before key.params key.args → answer.Admissible key.before key.results
  let base : Nat → HostRequest → HostReply := fun n key =>
    trappingHostChoice n key.before key.address key.identity key.params key.results key.args
  let selected := sourcePolicyOverride base occurrence request reply
  let choices : HostChoices := fun n before address identity params results args =>
    selected n ⟨before,address,identity,params,results,args⟩
  have admissible : ∀ n key, allowed key (selected n key) :=
    sourcePolicyOverride_preserves allowed base
      (fun n key => trappingHostChoice_admissible n key.before key.address key.identity key.params key.results key.args)
      occurrence request reply (fun _ _ _ => permitted)
  refine ⟨choices,?_,?_⟩
  · intro n before address identity params results args
    exact admissible n ⟨before,address,identity,params,results,args⟩
  · cases request
    exact sourcePolicyOverride_selected base occurrence _ reply

theorem memory_reply_selectable (occurrence : Nat) (before : meminst) (delta : Nat) (reply : Option meminst)
    (permitted : ∀ after, reply = some after → fun_growmemory before delta (some after)) :
    ∃ choices : MemoryGrowthChoices, choices.Admissible ∧ choices occurrence before delta = reply := by
  let allowed (key : meminst × Nat) (answer : Option meminst) : Prop :=
    ∀ after, answer = some after → fun_growmemory key.1 key.2 (some after)
  let base : Nat → meminst × Nat → Option meminst := fun _ _ => none
  let selected := sourcePolicyOverride base occurrence (before,delta) reply
  let choices : MemoryGrowthChoices := fun n old growth => selected n (old,growth)
  have admissible : ∀ n key, allowed key (selected n key) :=
    sourcePolicyOverride_preserves allowed base (by intro n key after impossible; cases impossible)
      occurrence (before,delta) reply permitted
  refine ⟨choices,?_,sourcePolicyOverride_selected base occurrence (before,delta) reply⟩
  intro n old growth after
  exact admissible n (old,growth) after

theorem table_reply_selectable (occurrence : Nat) (before : tableinst) (delta : Nat) (value : ref)
    (reply : Option tableinst)
    (permitted : ∀ after, reply = some after → fun_growtable before delta value (some after)) :
    ∃ choices : TableGrowthChoices, choices.Admissible ∧ choices occurrence before delta value = reply := by
  let allowed (key : tableinst × Nat × ref) (answer : Option tableinst) : Prop :=
    ∀ after, answer = some after → fun_growtable key.1 key.2.1 key.2.2 (some after)
  let base : Nat → tableinst × Nat × ref → Option tableinst := fun _ _ => none
  let selected := sourcePolicyOverride base occurrence (before,delta,value) reply
  let choices : TableGrowthChoices := fun n old growth fill => selected n (old,growth,fill)
  have admissible : ∀ n key, allowed key (selected n key) :=
    sourcePolicyOverride_preserves allowed base (by intro n key after impossible; cases impossible)
      occurrence (before,delta,value) reply permitted
  refine ⟨choices,?_,sourcePolicyOverride_selected base occurrence (before,delta,value) reply⟩
  intro n old growth fill after
  exact admissible n (old,growth,fill) after

end Exec.Spec

