import Exec.Theorems.Host.Open.Source.State.Single
import Exec.Theorems.Host.Open.Source.Chosen.ChosenLocalStep
import Exec.Theorems.Host.Open.Source.Chosen.PublishChosenStep
import Exec.Theorems.Host.Open.Source.Chosen.ChosenInvokeStep
import Exec.Theorems.Host.Open.Source.State.MissingStep
import Exec.Theorems.Host.Open.Source.Chosen.PureChoices
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem source_host_chosen_single {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (choices : SourceOperationChoices)
    (apiCompatible : SourceAPIChoicesCompatible memory allocator view choices)
    (publicationCompatible : SourcePublicationChoicesCompatible memory floats allocator view choices) (occurrence : Nat)
    (code : Store.CodeInterpretation) (native : State M) (source : Spec.OpenExecution.State SourceControl) (rank : Nat)
    (guard : SourceStateGuard memory allocator view code native source rank)
    (host : HostState) (hostSource : SourceHostState) (mode : native.mode=.host host)
    (sourceMode : source.mode=.host (.active hostSource))
    (represented : HostStateRepresents native.store.id hostSource host) :
    tick memory floats allocator select native ⦃out=>∃next,out=.cont next ∧
      ChosenSourceSingle memory allocator view select owner stop choices occurrence code native source rank next⦄ := by
  have localCase (localInstruction : ∀instruction,host.code[host.pc]?=some instruction →
      match instruction with | .invoke _ _ _ | .publish _ _ _ _=>False | _=>True) :
      tick memory floats allocator select native ⦃out=>∃next,out=.cont next ∧
        ChosenSourceSingle memory allocator view select owner stop choices occurrence code native source rank next⦄ := by
    exact source_local_chosen_single memory floats allocator correct allocation view laws select owner stop choices apiCompatible occurrence
      code native source rank guard host hostSource mode sourceMode represented localInstruction
  cases selected : host.code[host.pc]? with
  | none=>exact localCase (by intro instruction found;rw [selected] at found;cases found)
  | some instruction=>
    cases instruction with
    | invoke index values nextPC=>
      by_cases inside : index.val<native.store.funcs.length
      · obtain ⟨out,actual,next,nextSource,same,fresh,step,history⟩:=WP.spec_imp_exists
          (source_invoke_chosen_step memory floats allocator allocation view select owner stop choices occurrence code native source rank
            guard host hostSource mode sourceMode represented index values nextPC selected inside)
        subst out
        have storeEq : next.store=native.store:=by
          have equal:=actual
          simp only [tick,mode,selected,if_pos inside,runtime.interp.Execution.new,bind_ok] at equal
          obtain ⟨phase,called,equal⟩:=Itasca.ResultFacts.bind_ok_inv _ _ _ equal
          simp only [Result.ok.injEq,ControlFlow.cont.injEq] at equal
          exact (congrArg State.store equal).symm
        have effect : ReentrantCallbacks.Effect view code native.store code next.store:=by
          rw [storeEq]
          exact .refl guard.invariant
        rw [actual]
        exact WP.spec.ret ⟨next,rfl,.of_transition effect fresh step (sourceHistory_visible_append history)⟩
      · obtain ⟨next,nextSource,actual,fresh,step,history⟩:=source_missing_step memory floats allocator view select owner stop code
          native source rank guard host hostSource mode sourceMode represented index values nextPC selected inside
        have storeEq : next.store=native.store:=by
          have equal:=actual
          simp only [tick,mode,selected,if_neg inside,Result.ok.injEq,ControlFlow.cont.injEq] at equal
          exact (congrArg State.store equal).symm
        have effect : ReentrantCallbacks.Effect view code native.store code next.store:=by
          rw [storeEq]
          exact .refl guard.invariant
        have sourceSelected : hostSource.code[hostSource.pc]?=some (.invoke index values nextPC) := by
          simpa only [represented.1,represented.2.1] using selected
        have chosenStep:=choose_pure_host_transition choices occurrence step sourceMode
          (by intro instruction found;rw [sourceSelected,Option.some.injEq] at found;subst instruction;trivial)
        rw [actual]
        exact WP.spec.ret ⟨next,rfl,.of_transition effect fresh chosenStep (by simp only [history,visibleSourceHistory,List.flatMap_cons,visibleSourceObservation,List.flatMap_nil,List.nil_append,List.append_nil])⟩
    | publish bytes profile limits nextPC=>
      apply WP.spec_mono (source_publish_chosen_step memory floats allocator correct allocation view laws select owner stop choices publicationCompatible occurrence code native source rank
        guard host hostSource mode sourceMode represented bytes profile limits nextPC selected)
      rintro out ⟨next,afterCode,nextSource,rfl,effect,fresh,step,history⟩
      exact ⟨next,rfl,.of_transition effect fresh step (by simpa only [visibleSourceHistory,List.flatMap_cons,visibleSourceObservation,List.flatMap_nil,List.nil_append,List.append_nil] using history)⟩
    | returned values | trapped | jump target | branch condition yes no | returnAction segment | action segment nextPC=>
      exact localCase (by intro instruction found;rw [selected,Option.some.injEq] at found;subst instruction;trivial)
theorem source_host_chosen_tick {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (choices : SourceOperationChoices)
    (apiCompatible : SourceAPIChoicesCompatible memory allocator view choices)
    (publicationCompatible : SourcePublicationChoicesCompatible memory floats allocator view choices) (occurrence : Nat)
    (code : Store.CodeInterpretation) (native : State M) (source : Spec.OpenExecution.State SourceControl) (rank : Nat)
    (guard : SourceStateGuard memory allocator view code native source rank)
    (host : HostState) (hostSource : SourceHostState) (mode : native.mode=.host host)
    (sourceMode : source.mode=.host (.active hostSource))
    (represented : HostStateRepresents native.store.id hostSource host) :
    tick memory floats allocator select native ⦃out=>∃next,out=.cont next ∧
      ChosenSourceAdvance memory allocator view select owner stop choices occurrence code native source rank next⦄ := by
  apply WP.spec_mono (source_host_chosen_single memory floats allocator correct allocation view laws select owner stop choices apiCompatible publicationCompatible occurrence
    code native source rank guard host hostSource mode sourceMode represented)
  rintro out ⟨next,equal,single⟩
  exact ⟨next,equal,single.advance⟩
end Exec.Theorems.OpenReentrantControl
