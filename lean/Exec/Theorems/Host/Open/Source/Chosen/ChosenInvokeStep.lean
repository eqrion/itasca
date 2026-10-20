import Exec.Theorems.Host.Open.Source.Wasm.InvokeStep
import Exec.Theorems.Host.Open.Source.Chosen.ControlChoiceLifting
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall
/-- A nested request constructs its fresh native root guard and corresponding
source request together, retaining the parent's saved immutable control. -/
theorem source_invoke_chosen_step {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8)
    (select : Selector) (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (choices : SourceOperationChoices) (occurrence : Nat)
    (code : Store.CodeInterpretation) (native : State M) (source : Spec.OpenExecution.State SourceControl) (rank : Nat)
    (guard : SourceStateGuard memory allocator view code native source rank)
    (host : HostState) (hostSource : SourceHostState) (mode : native.mode=.host host)
    (sourceMode : source.mode=.host (.active hostSource))
    (represented : HostStateRepresents native.store.id hostSource host)
    (index : Usize) (values : Slice PureCallbacks.Literal) (nextPC : Nat)
    (selected : host.code[host.pc]?=some (.invoke index values nextPC)) (inside : index.val<native.store.funcs.length) :
    tick memory floats allocator select native ⦃out=>∃next nextSource,out=.cont next ∧
      SourceStateGuard memory allocator view code next nextSource 0 ∧
      Spec.OpenExecution.ChoiceTransition (sourceModel view (sourcePublication allocator view) select owner stop)
        (sourceControlChoices choices) occurrence source [.invokeEnter index.val ((OpenHostControl.literalValues values).val.map sourceValue)] nextSource ∧
      sourceHistory next.history=sourceHistory native.history++[.invokeEnter index.val ((OpenHostControl.literalValues values).val.map sourceValue)]⦄ := by
  apply WP.spec_mono (source_invoke_step memory floats allocator allocation view select owner stop code native source rank
    guard host hostSource mode sourceMode represented index values nextPC selected inside)
  rintro out ⟨next,nextSource,actual,held,step,history⟩
  refine ⟨next,nextSource,actual,held,choose_control_transition choices occurrence step ?_ (by simp),history⟩
  intro f body expected
  rw [sourceMode]
  simp
end Exec.Theorems.OpenReentrantControl
