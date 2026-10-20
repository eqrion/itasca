import Exec.Theorems.Host.Open.Source.State.ActiveWasmStep
import Exec.Theorems.Host.Open.Source.Chosen.WasmChosenTick
import Exec.Theorems.Host.Open.Source.Chosen.TickChosenCont
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- A guarded source Wasm configuration supplies both actual tick normality
and an exact silent-prefix description of its continued state or boundary. -/
theorem source_wasm_step_guarded {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (choices : SourceOperationChoices) (admissible : choices.wasm.Admissible)
    (numericChoice : choices.wasm.numeric=Spec.firstNumericChoice) (vectorChoice : choices.wasm.vector=Spec.firstVectorChoice)
    (compatible : GrowthChoicesCompatible memory allocator view choices.wasm) (occurrence : Nat)
    (code : Store.CodeInterpretation) (native : State M) (source : Spec.OpenExecution.State SourceControl) (rank : Nat)
    (guard : SourceStateGuard memory allocator view code native source rank)
    (f : frame) (body : List admininstr) (expected : resulttype) (sourceMode : source.mode=.wasm f body expected)
    (ownerEq : owner=native.store.id) (resources : SourceTickResources native.store.limits source)
    (available : Platform.AllocationAvailable allocator (2*Usize.max)) :
    tick memory floats allocator select native ⦃out=>∃next afterCode nextSource nextRank,out=.cont next ∧
      ReentrantCallbacks.Effect view code native.store afterCode next.store ∧
      SourceStateGuard memory allocator view afterCode next nextSource nextRank ∧
      WasmSourceStep choices occurrence select owner expected source.stack ⟨⟨source.store,f⟩,body⟩ native.history nextSource next.history⦄ := by
  rcases native with ⟨store,mode,stack,history⟩
  rcases source with ⟨sourceStore,sourceModeRaw,sourceStack⟩
  rcases guard with ⟨held,related,stackGuard,storeEq⟩
  dsimp only at sourceMode storeEq
  have guard:=SourceStateGuard.mk held related stackGuard storeEq
  cases related with
  | host raw hostSource represented => cases sourceMode
  | draft status values owned => cases sourceMode
  | preparing exec address signature args results phase metadata ready => cases sourceMode
  | finishing exec error root results signature metadata => cases sourceMode
  | returned answer sameStore issued => cases sourceMode
  | wasm signature world root results metadata typed =>
    cases sourceMode
    have decodedStore : (Abs.decode world.machine.source).1.1=sourceStore :=
      world.machine.invariant.storeEq.trans storeEq.symm
    have cfgEq : Abs.decode world.machine.source=⟨⟨sourceStore,(Abs.decode world.machine.source).1.2⟩,(Abs.decode world.machine.source).2⟩ := by
      generalize same : Abs.decode world.machine.source=configuration at decodedStore ⊢
      rcases configuration with ⟨⟨s,f⟩,body⟩
      dsimp only at decodedStore
      rw [decodedStore]
    have adequate:=resources world.machine.source cfgEq
    by_cases active : 0<world.machine.exec.frames.length
    · obtain ⟨out,computed,next,same,advance⟩:=WP.spec_imp_exists
        (source_wasm_chosen_tick memory floats allocator correct allocation view laws select owner stop choices admissible
          numericChoice vectorChoice compatible occurrence signature world _ _ guard rfl root results rfl rfl metadata typed ownerEq adequate available)
      subst out
      obtain ⟨afterCode,nextSource,nextRank,effect,fresh,step⟩:=source_active_wasm_step memory floats allocator correct allocation view laws
        select owner stop choices admissible numericChoice vectorChoice compatible occurrence signature world _ _ guard rfl
        root results rfl rfl metadata typed active ownerEq adequate available next computed
      rw [computed]
      exact WP.spec.ret ⟨next,afterCode,nextSource,nextRank,rfl,effect,fresh,by
        exact Eq.mp (congrArg (fun cfg=>WasmSourceStep choices occurrence select owner
          (.mk_list (signature.results.val.map sourceType)) sourceStack cfg history nextSource next.history) cfgEq) step⟩
    · have empty : world.machine.exec.frames.val=[] := by
        apply List.length_eq_zero_iff.mp
        change world.machine.exec.frames.length=0
        omega
      apply WP.spec_mono (source_finished_wasm_step memory floats allocator allocation view select owner stop choices occurrence signature
        world _ _ _ guard rfl root results rfl rfl metadata typed empty available)
      rintro out ⟨next,nextSource,same,effect,fresh,step⟩
      exact ⟨next,world.code,nextSource,0,same,effect,fresh,by
        exact Eq.mp (congrArg (fun cfg=>WasmSourceStep choices occurrence select owner
          (.mk_list (signature.results.val.map sourceType)) sourceStack cfg history nextSource next.history) cfgEq) step⟩
end Exec.Theorems.OpenReentrantControl
