import Exec.Theorems.Host.Open.Erasure.EraseHostCall
import Exec.Theorems.Host.Open.Erasure.EraseAppendTrace
import Exec.Theorems.Host.Open.Driver.CallbackReturnTrace
import Exec.Theorems.Host.Open.Native.NativeCallPartial
import Exec.Interp.Control.LoopTraceCompose
noncomputable section
namespace Exec.Theorems.OpenReentrantControl.Erased
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- An actual synchronous call return embeds its complete child callback trace
under the saved Wasm continuation and then follows the returned Wasm task. -/
theorem call_phase_lift {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (code : Store.CodeInterpretation) (before : runtime.store.Store M) (held : ExecutableInv view code before)
    (root : runtime.FuncAddr) (signature : Itasca.types.FuncType) (results : alloc.vec.Vec runtime.Value)
    (phase : CallPhase M Unit) (ready : CallTask memory view code before root signature phase)
    (out : Answer M Unit) (actual : resume memory (platform memory floats allocator select) phase=.ok out)
    {count : Nat} {answer : Outcome M}
    (suffix : NormalTrace (tick memory floats allocator select) count
      ⟨out.2.2.1,.wasm out.2.1 out.1 root results,[]⟩ answer) :
    ∃total,NormalTrace (tick memory floats allocator select) total (acceptCall select phase root results) answer := by
  cases phase with
  | done returned=>
    have same : returned=out := by simpa [resume] using actual
    subst returned
    exact ⟨count,suffix⟩
  | pending exec store token address base identity args defaults=>
    obtain ⟨sameStore,saved⟩ := ready
    subst store
    cases token
    simp only [resume] at actual
    obtain ⟨reply,callback,afterCallback⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
    rcases reply with ⟨hostStatus,token,after,values⟩
    cases token
    simp only [Std.uncurry] at afterCallback
    obtain ⟨pair,resumed,packed⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ afterCallback
    rcases pair with ⟨status,finished⟩
    simp only [Std.uncurry,Result.ok.injEq] at packed
    subst out
    obtain ⟨childCount,history,child⟩ := callback_return_trace memory floats allocator correct allocation view laws select code before held identity
      args.slice defaults.slice hostStatus after values callback
    have physical:=erase_normal_trace memory floats allocator select child
    have embedded:=append_host_trace memory floats allocator select hostStatus after values physical
      (show Shape (state (initialHost select before identity args.slice)) .host from .nil _) [.wasm exec address base root results]
    have resumedTick : tick memory floats allocator select
        ⟨after,.hostReturn hostStatus values,[.wasm exec address base root results]⟩=
        .ok (.cont ⟨after,.wasm finished status root results,[]⟩) := by
      simp [tick,restore,OpenReentrantControl.tick,resumed,Std.uncurry,output,state]
    refine ⟨childCount+(count+1),?_⟩
    exact embedded.followed_by (.next resumedTick suffix)
end Exec.Theorems.OpenReentrantControl.Erased
