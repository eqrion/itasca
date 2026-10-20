import Exec.Theorems.Host.Open.Driver.PlatformEffects
import Exec.Theorems.Host.Open.Driver.CallTask
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- Native synchronous call resumption is partially safe under the actual
combined callback implementation. A diverging child is permitted; any returned
reply supplies the checked effect required by its saved Wasm continuation. -/
theorem CallTask.resume_partial {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (select : Selector) {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    {root : runtime.FuncAddr} {signature : Itasca.types.FuncType} {phase : CallPhase M Unit}
    (held : ExecutableInv view code store) (ready : CallTask memory view code store root signature phase) :
    resume memory (platform memory floats allocator select) phase ⦃out=>∃afterCode,
      ReentrantCallbacks.Effect view code store afterCode out.2.2.1 ∧
      WasmTask view afterCode out.2.2.1 out.2.1 out.1 root signature⦄div := by
  cases phase with
  | done answer=>exact WP.spec_dspec _ _ _ (WP.spec.ret ready)
  | pending exec after token address base identity args defaults=>
    obtain ⟨sameStore,saved⟩ := ready
    subst after
    cases token
    have callback:=platform_partial_effects memory floats allocator correct allocation view laws select code store held () identity args.slice defaults.slice
    simp only [resume]
    generalize actual : (platform memory floats allocator select).call_host () store identity args.slice defaults.slice=result at callback ⊢
    cases callback with
    | div=>simp only [actual,bind_div];exact WP.dspec.div _
    | ret post=>
      rename_i reply
      rcases reply with ⟨status,token,after,values⟩
      cases token
      obtain ⟨afterCode,effect,issued⟩ := post
      obtain ⟨⟨status,finished⟩,resumed,task⟩ := WP.spec_imp_exists (saved afterCode after effect status values issued)
      simp only [actual,Std.uncurry,bind_ok,resumed]
      exact WP.dspec.ret ⟨afterCode,effect,task⟩
end Exec.Theorems.OpenReentrantControl
