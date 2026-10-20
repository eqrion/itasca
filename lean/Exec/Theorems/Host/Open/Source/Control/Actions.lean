import Exec.Theorems.Host.Open.Source.Control.Control
import Exec.Interp.Relations.TypedArguments
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp

/-- Native status is checked at the Wasm resumption boundary. Host control
retains the untyped proposed values until that check. -/
def sourceReply (status : HostStatus) (values : Slice runtime.Value) : Option (List val) :=
  match status with
  | .Ok _=>some (values.val.map sourceValue)
  | .Err _=>none

/-- Each finite API segment implements its independent source permission and
retains the exact decoded store, including committed effects on rejection. -/
theorem source_api_refines {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) (program : CallbackActions.Program) :
    program.run memory allocator store ⦃answer=>
      SourceAPI view program (Store.decodeStore view code store) (Store.decodeStore view code answer.2.1)
        (sourceReply answer.1 answer.2.2) ∧ OpenHostControl.Effect view code store answer.2.1 ∧
      ∀value∈answer.2.2.val,Store.ValueInStore answer.2.1 value⦄ := by
  apply WP.spec_mono (program.correct_owned memory allocator allocation view laws code store held)
  rintro ⟨status,after,values⟩ ⟨permission,effect,issued⟩
  exact ⟨⟨code,store,after,status,values.val,permission,rfl,rfl,rfl,effect.extension,effect.invariant.source_typed,issued⟩,effect,issued⟩

def SourceControlRepresents {M : Type} (owner : Usize) (source : SourceControl) (mode : Mode M) : Prop :=
  match source,mode with
  | .active h,.host raw=>HostStateRepresents owner h raw
  | .draft result,.hostReturn status values=>result=sourceReply status values ∧ ∀value∈values.val,OwnedBy owner value
  | _,_=>False

theorem HostStateRepresents.advance {owner : Usize} {h : SourceHostState} {raw : HostState}
    (held : HostStateRepresents owner h raw) (next : Nat) :
    HostStateRepresents owner {h with pc:=next} {raw with pc:=next} :=
  ⟨rfl,held.2⟩

/-- One actual local instruction is one independent source host action. The
separate publication policy and nested invocation are handled at their own
boundaries; no callback normality is used here. -/
theorem source_local_tick {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8)
    (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (publication : SourcePublication) (select : Selector) (state : State M)
    (held : ExecutableInv view code state.store) (raw : HostState) (mode : state.mode=.host raw)
    (source : SourceHostState) (represented : HostStateRepresents state.store.id source raw)
    (localInstruction : ∀instruction,raw.code[raw.pc]?=some instruction →
      match instruction with | .invoke _ _ _ | .publish _ _ _ _=>False | _=>True) :
    tick memory floats allocator select state ⦃out=>∃next control,out=.cont next ∧
      next.stack=state.stack ∧ next.history=state.history ∧
      OpenHostControl.Effect view code state.store next.store ∧
      SourceAction view publication (Store.decodeStore view code state.store) (.active source)
        (Store.decodeStore view code next.store) control ∧
      SourceControlRepresents state.store.id control next.mode⦄ := by
  have selectedSource : ∀instruction,raw.code[raw.pc]?=instruction → source.code[source.pc]?=instruction := by
    intro instruction selected
    simpa only [represented.1,represented.2.1] using selected
  unfold tick
  rw [mode]
  dsimp only
  cases selected : raw.code[raw.pc]? with
  | none=>
    exact WP.spec.ret ⟨_,.draft none,rfl,rfl,rfl,.refl held,.missing (selectedSource _ selected),⟨rfl,by simp⟩⟩
  | some instruction=>
    cases instruction with
    | trapped=>
      exact WP.spec.ret ⟨_,.draft none,rfl,rfl,rfl,.refl held,.trapped (selectedSource _ selected),⟨rfl,by simp⟩⟩
    | returned values=>
      exact WP.spec.ret ⟨_,.draft _,rfl,rfl,rfl,.refl held,.returned (selectedSource _ selected),⟨rfl,by
        intro value member
        exact ((PureCallbacks.Program.returned values).in_store state.store value member).1.owned⟩⟩
    | jump target=>
      exact WP.spec.ret ⟨_,.active _,rfl,rfl,rfl,.refl held,.jump (selectedSource _ selected),represented.advance target⟩
    | branch condition yes no=>
      exact WP.spec.ret ⟨_,.active _,rfl,rfl,rfl,.refl held,.branch (selectedSource _ selected),represented.advance _⟩
    | action segment next=>
      dsimp only
      obtain ⟨⟨status,after,values⟩,actual,permission,effect,owned⟩ := WP.spec_imp_exists
        (source_api_refines memory allocator allocation view laws code state.store held segment)
      rw [actual,bind_ok]
      cases status with
      | Ok unit=>
        cases unit
        exact WP.spec.ret ⟨_,.active _,rfl,rfl,rfl,effect,.action (selectedSource _ selected) permission,represented.advance next⟩
      | Err error=>
        exact WP.spec.ret ⟨_,.draft none,rfl,rfl,rfl,effect,.rejected (selectedSource _ selected) permission,⟨rfl,by
          intro value member
          have belongs : OwnedBy after.id value := (owned value member).1.owned
          have identity : after.id=state.store.id := effect.metadata.identity
          exact identity ▸ belongs⟩⟩
    | returnAction segment=>
      dsimp only
      obtain ⟨⟨status,after,values⟩,actual,permission,effect,owned⟩ := WP.spec_imp_exists
        (source_api_refines memory allocator allocation view laws code state.store held segment)
      rw [actual,bind_ok]
      exact WP.spec.ret ⟨_,.draft _,rfl,rfl,rfl,effect,.returnAction (selectedSource _ selected) permission,⟨rfl,by
        intro value member
        have belongs : OwnedBy after.id value := (owned value member).1.owned
        have identity : after.id=state.store.id := effect.metadata.identity
        exact identity ▸ belongs⟩⟩
    | invoke index args next=>exact False.elim (localInstruction _ selected)
    | publish bytes profile limits next=>exact False.elim (localInstruction _ selected)
end Exec.Theorems.OpenReentrantControl
