import Exec.Theorems.Host.Open.Source.Control.Actions
import Exec.Theorems.Host.Open.Source.Control.Publication
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp

/-- Publication is one independently permitted source action at the reached
code interpretation. Rejection retains committed effects and produces a draft
host trap; the observable host exit is emitted by the following native tick. -/
theorem source_publish_tick {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (select : Selector) (state : State M) (held : ExecutableInv view code state.store)
    (host : HostState) (mode : state.mode=.host host) (source : SourceHostState)
    (represented : HostStateRepresents state.store.id source host)
    (bytes : Slice U8) (profile : Itasca.ValidationProfile) (limits : runtime.compiler.CompileLimits) (next : Nat)
    (selected : host.code[host.pc]?=some (.publish bytes profile limits next)) :
    tick memory floats allocator select state ⦃out=>∃after afterCode control,out=.cont after ∧
      after.stack=state.stack ∧ after.history=state.history ∧
      ReentrantCallbacks.Effect view code state.store afterCode after.store ∧
      SourceAction view (sourcePublication allocator view) (Store.decodeStore view code state.store) (.active source)
        (Store.decodeStore view afterCode after.store) control ∧
      SourceControlRepresents state.store.id control after.mode⦄ := by
  have sourceSelected : source.code[source.pc]?=some (.publish bytes profile limits next) := by
    simpa only [represented.1,represented.2.1] using selected
  unfold tick
  rw [mode]
  dsimp only
  rw [selected]
  dsimp only
  obtain ⟨⟨status,after⟩,actual,afterCode,effect,permission⟩ := WP.spec_imp_exists
    (publish_source memory floats allocator correct allocation view laws code state.store held bytes profile limits)
  rw [actual,bind_ok]
  cases status with
  | Ok unit=>
    cases unit
    exact WP.spec.ret ⟨_,afterCode,.active _,rfl,rfl,rfl,effect,
      .publish (accepted:=true) sourceSelected permission,represented.advance next⟩
  | Err error=>
    exact WP.spec.ret ⟨_,afterCode,.draft none,rfl,rfl,rfl,effect,
      .publish (accepted:=false) sourceSelected permission,⟨rfl,by simp⟩⟩
end Exec.Theorems.OpenReentrantControl
