import Exec.Spec.Open.Execution
import Exec.Theorems.Host.Open.Source.State.Selector
noncomputable section
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp SpecExt

/-- A checked API leaf is specified by the independent operation relation,
with decoded stores and values. It contains no execution equation. -/
def SourceAPI {M : Type} (view : M → Slice U8) (program : CallbackActions.Program)
    (before after : store) (result : Option (List val)) : Prop :=
  ∃code rawBefore rawAfter status values,
    CallbackActions.Returns view code program rawBefore status rawAfter values ∧
    Store.decodeStore view code rawBefore=before ∧ Store.decodeStore view code rawAfter=after ∧
    result=(match status with | .Ok _=>some (values.map sourceValue) | .Err _=>none) ∧
    Extend_store before after ∧ Store_ok after ∧ ∀value∈values,Store.ValueInStore rawAfter value

/-- Publication permissions are a separate source policy. Implementations must
justify this policy from compilation and instantiation, including rejection. -/
structure SourcePublication where
  effect : Slice U8 → Itasca.ValidationProfile → runtime.compiler.CompileLimits →
    store → store → Bool → Prop
  preserves : ∀bytes profile limits s t accepted,effect bytes profile limits s t accepted →
    Store_ok s → Extend_store s t ∧ Store_ok t

inductive SourceControl where
  | active (state : SourceHostState)
  | draft (result : Option (List val))

def sourceResume (control : SourceControl) : Spec.OpenExecution.InvocationResult → SourceControl
  | .returned _=>control
  | _=>.draft none

/-- Immutable host control steps. API failures retain their committed store;
request/return nesting is handled by the independent combined source machine. -/
inductive SourceAction {M : Type} (view : M → Slice U8) (publication : SourcePublication) :
    store → SourceControl → store → SourceControl → Prop
  | missing {s h} (selected : h.code[h.pc]?=none) :
      SourceAction view publication s (.active h) s (.draft none)
  | trapped {s h} (selected : h.code[h.pc]?=some .trapped) :
      SourceAction view publication s (.active h) s (.draft none)
  | returned {s h values} (selected : h.code[h.pc]?=some (.returned values)) :
      SourceAction view publication s (.active h) s
        (.draft (some ((OpenHostControl.literalValues values).val.map sourceValue)))
  | missingFunction {s h index arguments next}
      (selected : h.code[h.pc]?=some (.invoke index arguments next)) (outside : ¬index.val<s.FUNCS.length) :
      SourceAction view publication s (.active h) s (.draft none)
  | jump {s h target} (selected : h.code[h.pc]?=some (.jump target)) :
      SourceAction view publication s (.active h) s (.active {h with pc:=target})
  | branch {s h condition yes no} (selected : h.code[h.pc]?=some (.branch condition yes no)) :
      SourceAction view publication s (.active h) s (.active {h with pc:=if condition then yes else no})
  | action {s t h segment next values} (selected : h.code[h.pc]?=some (.action segment next))
      (effect : SourceAPI view segment s t (some values)) :
      SourceAction view publication s (.active h) t (.active {h with pc:=next})
  | rejected {s t h segment next} (selected : h.code[h.pc]?=some (.action segment next))
      (effect : SourceAPI view segment s t none) :
      SourceAction view publication s (.active h) t (.draft none)
  | returnAction {s t h segment result} (selected : h.code[h.pc]?=some (.returnAction segment))
      (effect : SourceAPI view segment s t result) :
      SourceAction view publication s (.active h) t (.draft result)
  | publish {s t h bytes profile limits next accepted}
      (selected : h.code[h.pc]?=some (.publish bytes profile limits next))
      (effect : publication.effect bytes profile limits s t accepted) :
      SourceAction view publication s (.active h) t
        (if accepted then .active {h with pc:=next} else .draft none)

theorem SourceAction.preserves {M : Type} {view : M → Slice U8} {publication : SourcePublication}
    {s t : store} {h k : SourceControl} (action : SourceAction view publication s h t k)
    (typed : Store_ok s) : Extend_store s t ∧ Store_ok t := by
  cases action with
  | missing selected | trapped selected | returned selected | missingFunction selected outside | jump selected | branch selected =>
    exact ⟨Spec.extend_store_refl _ (by cases typed; assumption),typed⟩
  | action selected effect | rejected selected effect | returnAction selected effect =>
    obtain ⟨code,before,after,status,values,permission,decodedBefore,decodedAfter,result,extension,fresh,owned⟩ := effect
    exact ⟨extension,fresh⟩
  | publish selected effect => exact publication.preserves _ _ _ _ _ _ effect typed

inductive SourceRequest : SourceControl → funcaddr → List val → SourceControl → Prop
  | invoke {h index arguments next} (selected : h.code[h.pc]?=some (.invoke index arguments next)) :
      SourceRequest (.active h) index.val
        ((OpenHostControl.literalValues arguments).val.map sourceValue) (.active {h with pc:=next})

inductive SourceFinish : store → SourceControl → Option (List val) → Prop
  | draft {s result} : SourceFinish s (.draft result) result

def sourceModel {M : Type} (view : M → Slice U8) (publication : SourcePublication)
    (select : Selector) (owner : Usize)
    (stop : Spec.OpenExecution.StopReason → config → Prop) : Spec.OpenExecution.HostModel SourceControl where
  enter identity args:=.active (sourceHostEntry select owner identity args)
  action:=SourceAction view publication
  action_preserves:=fun _ _ _ _ step typed=>step.preserves typed
  invoke:=SourceRequest
  finish:=SourceFinish
  resume:=sourceResume
  permitsStop:=stop

end Exec.Theorems.OpenReentrantControl
