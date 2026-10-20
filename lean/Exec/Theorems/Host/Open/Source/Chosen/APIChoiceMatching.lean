import Exec.Theorems.Host.Open.Source.Chosen.ControlChoices
import Exec.Theorems.Host.Open.Source.Control.Actions
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Compatibility concerns one finite checked API segment and its ordinary
result. Segment normality and permission are proved independently by the
implementation theorem; no host-control or whole-invocation return is assumed. -/
def SourceAPIChoicesCompatible {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (view : M → Slice U8) (choices : SourceOperationChoices) : Prop:=
  ∀occurrence code store,ExecutableInv view code store → ∀program answer,
    CallbackActions.Program.run memory allocator program store=.ok answer →
    choices.api occurrence (Store.decodeStore view code store) program=
      some ⟨Store.decodeStore view code answer.2.1,sourceReply answer.1 answer.2.2⟩

/-- Actual finite API operations construct the source permission and effect
and match the independently selected result under primitive API compatibility. -/
theorem source_api_chosen {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (choices : SourceOperationChoices)
    (compatible : SourceAPIChoicesCompatible memory allocator view choices)
    (occurrence : Nat) (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (held : ExecutableInv view code store) (program : CallbackActions.Program) :
    program.run memory allocator store ⦃answer=>
      SourceAPI view program (Store.decodeStore view code store) (Store.decodeStore view code answer.2.1)
        (sourceReply answer.1 answer.2.2) ∧ OpenHostControl.Effect view code store answer.2.1 ∧
      (∀value∈answer.2.2.val,Store.ValueInStore answer.2.1 value) ∧
      choices.api occurrence (Store.decodeStore view code store) program=
        some ⟨Store.decodeStore view code answer.2.1,sourceReply answer.1 answer.2.2⟩⦄ := by
  obtain ⟨answer,actual,permission,effect,owned⟩:=WP.spec_imp_exists
    (source_api_refines memory allocator allocation view laws code store held program)
  rw [actual]
  exact WP.spec.ret ⟨permission,effect,owned,compatible occurrence code store held program answer actual⟩
end Exec.Theorems.OpenReentrantControl
