import Exec.Theorems.Host.Open.Source.Chosen.APIChoiceMatching
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem source_local_chosen_tick {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8)
    (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (publication : SourcePublication) (choices : SourceOperationChoices)
    (compatible : SourceAPIChoicesCompatible memory allocator view choices) (occurrence : Nat) (select : Selector) (state : State M)
    (held : ExecutableInv view code state.store) (raw : HostState) (mode : state.mode=.host raw)
    (source : SourceHostState) (represented : HostStateRepresents state.store.id source raw)
    (localInstruction : ∀instruction,raw.code[raw.pc]?=some instruction →
      match instruction with | .invoke _ _ _ | .publish _ _ _ _=>False | _=>True) :
    tick memory floats allocator select state ⦃out=>∃next control,out=.cont next ∧
      next.stack=state.stack ∧ next.history=state.history ∧
      OpenHostControl.Effect view code state.store next.store ∧
      SourceAction view publication (Store.decodeStore view code state.store) (.active source)
        (Store.decodeStore view code next.store) control ∧
      chosenSourceAction choices occurrence (Store.decodeStore view code state.store) (.active source)=
        some (Store.decodeStore view code next.store,control) ∧
      SourceControlRepresents state.store.id control next.mode⦄ := by
  have selectedSource : ∀instruction,raw.code[raw.pc]?=instruction → source.code[source.pc]?=instruction := by
    intro instruction selected
    simpa only [represented.1,represented.2.1] using selected
  unfold tick
  rw [mode]
  dsimp only
  cases selected : raw.code[raw.pc]? with
  | none=>
    exact WP.spec.ret ⟨_,.draft none,rfl,rfl,rfl,.refl held,.missing (selectedSource _ selected),by simp only [chosenSourceAction,selectedSource _ selected],⟨rfl,by simp⟩⟩
  | some instruction=>
    cases instruction with
    | trapped=>
      exact WP.spec.ret ⟨_,.draft none,rfl,rfl,rfl,.refl held,.trapped (selectedSource _ selected),by simp only [chosenSourceAction,selectedSource _ selected],⟨rfl,by simp⟩⟩
    | returned values=>
      exact WP.spec.ret ⟨_,.draft _,rfl,rfl,rfl,.refl held,.returned (selectedSource _ selected),by simp only [chosenSourceAction,selectedSource _ selected],⟨rfl,by
        intro value member
        exact ((PureCallbacks.Program.returned values).in_store state.store value member).1.owned⟩⟩
    | jump target=>
      exact WP.spec.ret ⟨_,.active _,rfl,rfl,rfl,.refl held,.jump (selectedSource _ selected),by simp only [chosenSourceAction,selectedSource _ selected],represented.advance target⟩
    | branch condition yes no=>
      exact WP.spec.ret ⟨_,.active _,rfl,rfl,rfl,.refl held,.branch (selectedSource _ selected),by simp only [chosenSourceAction,selectedSource _ selected],represented.advance _⟩
    | action segment next=>
      dsimp only
      obtain ⟨⟨status,after,values⟩,actual,permission,effect,owned,chosen⟩ := WP.spec_imp_exists
        (source_api_chosen memory allocator allocation view laws choices compatible occurrence code state.store held segment)
      rw [actual,bind_ok]
      cases status with
      | Ok unit=>
        cases unit
        exact WP.spec.ret ⟨_,.active _,rfl,rfl,rfl,effect,.action (selectedSource _ selected) permission,by simp only [chosenSourceAction,selectedSource _ selected,chosen,Option.map_some,sourceReply],represented.advance next⟩
      | Err error=>
        exact WP.spec.ret ⟨_,.draft none,rfl,rfl,rfl,effect,.rejected (selectedSource _ selected) permission,by simp only [chosenSourceAction,selectedSource _ selected,chosen,Option.map_some,sourceReply],⟨rfl,by
          intro value member
          have belongs : OwnedBy after.id value := (owned value member).1.owned
          have identity : after.id=state.store.id := effect.metadata.identity
          exact identity ▸ belongs⟩⟩
    | returnAction segment=>
      dsimp only
      obtain ⟨⟨status,after,values⟩,actual,permission,effect,owned,chosen⟩ := WP.spec_imp_exists
        (source_api_chosen memory allocator allocation view laws choices compatible occurrence code state.store held segment)
      rw [actual,bind_ok]
      exact WP.spec.ret ⟨_,.draft _,rfl,rfl,rfl,effect,.returnAction (selectedSource _ selected) permission,by simp only [chosenSourceAction,selectedSource _ selected,chosen,Option.map_some,sourceReply],⟨rfl,by
        intro value member
        have belongs : OwnedBy after.id value := (owned value member).1.owned
        have identity : after.id=state.store.id := effect.metadata.identity
        exact identity ▸ belongs⟩⟩
    | invoke index args next=>exact False.elim (localInstruction _ selected)
    | publish bytes profile limits next=>exact False.elim (localInstruction _ selected)
end Exec.Theorems.OpenReentrantControl
