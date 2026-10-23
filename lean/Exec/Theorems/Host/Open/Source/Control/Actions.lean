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

end Exec.Theorems.OpenReentrantControl
