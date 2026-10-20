import Exec.Theorems.Host.Open.Source.State.TickCont
import Exec.Theorems.Host.Open.Driver.DriverPrefixes
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Divergence of the actual guarded driver yields a productive trace of the
independent combined Wasm/host machine. Empty administrative advances cannot
supply infinitely many native ticks without source progress. -/
theorem run_source_infinite {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (code : Store.CodeInterpretation) (native : State M) (source : Spec.OpenExecution.State SourceControl) (rank : Nat)
    (guard : SourceStateGuard memory allocator view code native source rank)
    (shape : native.Shape .invocation) (noOverflow : NoOverflowMode native.mode)
    (ownerEq : owner=native.store.id) (allowed : ∀reason configuration,stop reason configuration)
    (divergent : run memory floats allocator select native=.div) :
    Spec.OpenExecution.InfiniteTrace (sourceModel view (sourcePublication allocator view) select owner stop) source := by
  classical
  let Point:={p : State M × Store.CodeInterpretation × Spec.OpenExecution.State SourceControl × Nat //
    SourceStateGuard memory allocator view p.2.1 p.1 p.2.2.1 p.2.2.2 ∧
    p.1.Shape .invocation ∧ NoOverflowMode p.1.mode ∧ owner=p.1.store.id ∧
    run memory floats allocator select p.1=.div}
  let sourceOf (point : Point):=point.val.2.2.1
  let rankOf (point : Point):=point.val.2.2.2
  let model:=sourceModel view (sourcePublication allocator view) select owner stop
  have advance : ∀point : Point,∃next count events,
      Spec.OpenExecution.Trace model count (sourceOf point) events (sourceOf next) ∧
      (count=0 → rankOf next<rankOf point) := by
    rintro ⟨⟨current,currentCode,currentSource,currentRank⟩,held,shaped,safe,owned,diverges⟩
    obtain ⟨states,initial,steps⟩:=run_divergent_stream memory floats allocator correct allocation view laws select currentCode current held.native diverges
    have firstStep:=(steps 0).2.1
    rw [initial] at firstStep
    have nextDiverges:=(steps 1).2.2.1
    obtain ⟨afterCode,nextSource,afterRank,count,events,effect,fresh,path,decrease,observed⟩:=
      source_tick_cont memory floats allocator correct allocation view laws select owner stop currentCode current currentSource currentRank
        held shaped safe owned allowed (states 1) firstStep
    have nextShape:=tick_shape memory floats allocator select current .invocation shaped (.cont (states 1)) firstStep
    have nextSafe:=tick_no_overflow memory floats allocator correct allocation view laws select currentCode current held.invariant safe (.cont (states 1)) firstStep
    have nextOwner : owner=(states 1).store.id:=owned.trans effect.metadata.identity.symm
    let next : Point:=⟨⟨states 1,afterCode,nextSource,afterRank⟩,fresh,nextShape,nextSafe,nextOwner,nextDiverges⟩
    exact ⟨next,count,events,path,decrease⟩
  let initial : Point:=⟨⟨native,code,source,rank⟩,guard,shape,noOverflow,ownerEq,divergent⟩
  exact Spec.OpenExecution.infinite_of_decreasing_stutter model sourceOf rankOf advance initial
end Exec.Theorems.OpenReentrantControl
