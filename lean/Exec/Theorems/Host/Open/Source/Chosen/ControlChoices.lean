import Exec.Spec.Open.ExecutionChoices
import Exec.Theorems.Host.Open.Source.Control.Control
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Source policies for finite API segments and publication, alongside explicit
Wasm primitive policies. Undefined requests are allowed outside represented
source stores; native compatibility separately requires reachable requests to
be selected. No policy is defined from an interpreter result. -/
structure SourceOperationChoices where
  wasm : Spec.SourceChoices
  api : Nat → store → CallbackActions.Program → Option Spec.HostReply
  publish : Nat → store → Slice U8 → Itasca.ValidationProfile → runtime.compiler.CompileLimits → Option (store × Bool)

structure SourceOperationChoices.Admissible {M : Type} (view : M → Slice U8)
    (publication : SourcePublication) (choices : SourceOperationChoices) : Prop where
  wasm : choices.wasm.Admissible
  api : ∀occurrence s program reply,choices.api occurrence s program=some reply →
    SourceAPI view program s reply.after reply.result
  publish : ∀occurrence s bytes profile limits after accepted,
    choices.publish occurrence s bytes profile limits=some (after,accepted) →
    publication.effect bytes profile limits s after accepted

def chosenSourceAction (choices : SourceOperationChoices) (occurrence : Nat) (s : store) :
    SourceControl → Option (store × SourceControl)
  | .draft _=>none
  | .active h=>match h.code[h.pc]? with
    | none | some .trapped=>some (s,.draft none)
    | some (.returned values)=>some (s,.draft (some ((OpenHostControl.literalValues values).val.map sourceValue)))
    | some (.jump target)=>some (s,.active {h with pc:=target})
    | some (.branch condition yes no)=>some (s,.active {h with pc:=if condition then yes else no})
    | some (.invoke index _ _)=>if index.val<s.FUNCS.length then none else some (s,.draft none)
    | some (.action program next)=> (choices.api occurrence s program).map (fun reply=>(reply.after,
        match reply.result with | some _=>.active {h with pc:=next} | none=>.draft none))
    | some (.returnAction program)=> (choices.api occurrence s program).map (fun reply=>(reply.after,.draft reply.result))
    | some (.publish bytes profile limits next)=> (choices.publish occurrence s bytes profile limits).map
        (fun answer=>(answer.1,if answer.2 then .active {h with pc:=next} else .draft none))

def chosenSourceInvoke (_occurrence : Nat) : SourceControl → Option (funcaddr × List val × SourceControl)
  | .draft _=>none
  | .active h=>match h.code[h.pc]? with
    | some (.invoke index args next)=>some (index.val,(OpenHostControl.literalValues args).val.map sourceValue,.active {h with pc:=next})
    | _=>none

def chosenSourceFinish (_occurrence : Nat) (_s : store) : SourceControl → Option (Option (List val))
  | .draft result=>some result
  | .active _=>none

def sourceControlChoices (choices : SourceOperationChoices) : Spec.OpenExecution.Choices SourceControl:=
  ⟨choices.wasm,chosenSourceAction choices,chosenSourceInvoke,chosenSourceFinish⟩

/-- Selecting source API and publication permissions constructs an admissible
combined choice model. Local control, invocation requests and draft replies
are derived from the immutable source program. -/
theorem sourceControlChoices_admissible {M : Type} (view : M → Slice U8) (publication : SourcePublication)
    (select : Selector) (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (choices : SourceOperationChoices) (allowed : choices.Admissible view publication) :
    (sourceControlChoices choices).Admissible (sourceModel view publication select owner stop) := by
  refine ⟨allowed.wasm,?_,?_,?_⟩
  · intro occurrence s control t next actual
    cases control with
    | draft result=>cases actual
    | active h=>
      cases selected : h.code[h.pc]? with
      | none=>
        simp only [sourceControlChoices,chosenSourceAction,selected,Option.some.injEq,Prod.mk.injEq] at actual
        obtain ⟨rfl,rfl⟩:=actual
        exact .missing selected
      | some instruction=>
        cases instruction with
        | trapped=>
          simp only [sourceControlChoices,chosenSourceAction,selected,Option.some.injEq,Prod.mk.injEq] at actual
          obtain ⟨rfl,rfl⟩:=actual
          exact .trapped selected
        | returned values=>
          simp only [sourceControlChoices,chosenSourceAction,selected,Option.some.injEq,Prod.mk.injEq] at actual
          obtain ⟨rfl,rfl⟩:=actual
          exact .returned selected
        | jump target=>
          simp only [sourceControlChoices,chosenSourceAction,selected,Option.some.injEq,Prod.mk.injEq] at actual
          obtain ⟨rfl,rfl⟩:=actual
          exact .jump selected
        | branch condition yes no=>
          simp only [sourceControlChoices,chosenSourceAction,selected,Option.some.injEq,Prod.mk.injEq] at actual
          obtain ⟨rfl,rfl⟩:=actual
          exact .branch selected
        | invoke index args nextPC=>
          by_cases inside : index.val<s.FUNCS.length
          · simp only [sourceControlChoices,chosenSourceAction,selected,if_pos inside] at actual
            cases actual
          · simp only [sourceControlChoices,chosenSourceAction,selected,if_neg inside,Option.some.injEq,Prod.mk.injEq] at actual
            obtain ⟨rfl,rfl⟩:=actual
            exact .missingFunction selected inside
        | returnAction program=>
          cases chosen : choices.api occurrence s program with
          | none=>simp only [sourceControlChoices,chosenSourceAction,selected,chosen,Option.map_none] at actual;cases actual
          | some reply=>
            simp only [sourceControlChoices,chosenSourceAction,selected,chosen,Option.map_some,Option.some.injEq,Prod.mk.injEq] at actual
            obtain ⟨rfl,rfl⟩:=actual
            exact .returnAction selected (allowed.api occurrence s program reply chosen)
        | action program nextPC=>
          cases chosen : choices.api occurrence s program with
          | none=>simp only [sourceControlChoices,chosenSourceAction,selected,chosen,Option.map_none] at actual;cases actual
          | some reply=>
            cases result : reply.result with
            | none=>
              simp only [sourceControlChoices,chosenSourceAction,selected,chosen,Option.map_some,result,Option.some.injEq,Prod.mk.injEq] at actual
              obtain ⟨rfl,rfl⟩:=actual
              exact .rejected selected (by simpa only [result] using allowed.api occurrence s program reply chosen)
            | some values=>
              simp only [sourceControlChoices,chosenSourceAction,selected,chosen,Option.map_some,result,Option.some.injEq,Prod.mk.injEq] at actual
              obtain ⟨rfl,rfl⟩:=actual
              exact .action selected (by simpa only [result] using allowed.api occurrence s program reply chosen)
        | publish bytes profile limits nextPC=>
          cases chosen : choices.publish occurrence s bytes profile limits with
          | none=>simp only [sourceControlChoices,chosenSourceAction,selected,chosen,Option.map_none] at actual;cases actual
          | some answer=>
            rcases answer with ⟨after,accepted⟩
            simp only [sourceControlChoices,chosenSourceAction,selected,chosen,Option.map_some,Option.some.injEq,Prod.mk.injEq] at actual
            obtain ⟨rfl,rfl⟩:=actual
            exact .publish selected (allowed.publish occurrence s bytes profile limits after accepted chosen)
  · intro occurrence control address args next actual
    cases control with
    | draft result=>cases actual
    | active h=>
      cases selected : h.code[h.pc]? with
      | none=>simp only [sourceControlChoices,chosenSourceInvoke,selected] at actual;cases actual
      | some instruction=>
        cases instruction <;> simp only [sourceControlChoices,chosenSourceInvoke,selected] at actual
        all_goals cases actual
        exact .invoke selected
  · intro occurrence s control result actual
    cases control with
    | active h=>cases actual
    | draft proposed=>
      have equal : proposed=result:=Option.some.inj actual
      subst result
      exact .draft
end Exec.Theorems.OpenReentrantControl
