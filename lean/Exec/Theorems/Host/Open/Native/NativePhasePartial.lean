import Exec.Theorems.Host.Open.Native.NativeExecutePartial
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- Prepared native invocation remains safe with partial combined callbacks;
all ordinary API answers retain cumulative effects and issued successful values. -/
theorem native_phase_partial {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (phase : InvokePhase M Unit) (task : InvokeTask memory view code store phase) :
    eraseInvoke memory (platform memory floats allocator select) floats allocator phase ⦃out=>∃afterCode,
      ReentrantCallbacks.Effect view code store afterCode out.2.2.1 ∧
      (out.1=.Ok () → ∀value∈out.2.2.2.2.val,Store.IssuedValue out.2.2.1 value)⦄div := by
  cases phase with
  | done answer=>
    obtain ⟨sameStore,error,status⟩ := task
    apply WP.dspec.ret
    refine ⟨code,?_,?_⟩
    · rw [sameStore];exact .refl held
    · intro impossible
      rw [status] at impossible
      cases impossible
  | waiting phase root results=>
    obtain ⟨signature,ready⟩ := task
    rw [eraseInvoke_waiting]
    have safe:=ready.resume_partial memory floats allocator correct allocation view laws select held
    generalize actual : resume memory (platform memory floats allocator select) phase=result at safe ⊢
    cases safe with
    | div=>simp only [bind_div];exact WP.dspec.div _
    | ret post=>
      rename_i out
      obtain ⟨afterCode,effect,afterTask⟩ := post
      simp only [bind_ok]
      apply WP.dspec_mono (native_execute_partial memory floats allocator correct allocation view laws select afterCode
        (out.2.1,out.2.2.1,out.2.2.2,out.1) effect.invariant root signature afterTask results)
      rintro answer ⟨finalCode,more,issued⟩
      exact ⟨finalCode,effect.trans more,issued⟩
end Exec.Theorems.OpenReentrantControl
