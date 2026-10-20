import Exec.Theorems.Host.Open.Source.Chosen.ControlChoices
import Exec.Theorems.Host.Open.Source.Control.Publication
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Leaf compatibility for the selected publication outcome. Ordinary return,
source permission and code/store preservation are proved separately by the
compiler/instantiator implementation theorem. This law assumes none of those
facts for a whole host interaction or nested invocation. -/
def SourcePublicationChoicesCompatible {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (choices : SourceOperationChoices) : Prop :=
  ∀occurrence code (store : runtime.store.Store M),ExecutableInv view code store →
    ∀bytes profile limits answer afterCode,
      publish memory floats allocator store bytes profile limits=.ok answer →
      ReentrantCallbacks.Effect view code store afterCode answer.2 →
      SourcePublicationEffect allocator view bytes profile limits (Store.decodeStore view code store)
        (Store.decodeStore view afterCode answer.2) (match answer.1 with | .Ok _=>true | .Err _=>false) →
      choices.publish occurrence (Store.decodeStore view code store) bytes profile limits=
        some (Store.decodeStore view afterCode answer.2,match answer.1 with | .Ok _=>true | .Err _=>false)

theorem publish_source_chosen {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (choices : SourceOperationChoices) (compatible : SourcePublicationChoicesCompatible memory floats allocator view choices)
    (occurrence : Nat) (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (held : ExecutableInv view code store) (bytes : Slice U8) (profile : Itasca.ValidationProfile)
    (limits : runtime.compiler.CompileLimits) :
    publish memory floats allocator store bytes profile limits ⦃answer=>∃afterCode,
      ReentrantCallbacks.Effect view code store afterCode answer.2 ∧
      SourcePublicationEffect allocator view bytes profile limits (Store.decodeStore view code store)
        (Store.decodeStore view afterCode answer.2) (match answer.1 with | .Ok _=>true | .Err _=>false) ∧
      choices.publish occurrence (Store.decodeStore view code store) bytes profile limits=
        some (Store.decodeStore view afterCode answer.2,match answer.1 with | .Ok _=>true | .Err _=>false)⦄ := by
  obtain ⟨answer,actual,afterCode,effect,permission⟩:=WP.spec_imp_exists
    (publish_source memory floats allocator correct allocation view laws code store held bytes profile limits)
  rw [actual]
  exact WP.spec.ret ⟨afterCode,effect,permission,compatible occurrence code store held bytes profile limits answer afterCode actual effect permission⟩
end Exec.Theorems.OpenReentrantControl
