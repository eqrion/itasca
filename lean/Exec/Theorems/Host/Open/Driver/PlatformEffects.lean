import Exec.Theorems.Host.Open.Driver.DriverPrefixes
import Exec.Theorems.Host.Open.Driver.StackTraces
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std

/-- The actual synchronous callback retains every checked effect on return;
it may instead diverge through a productive combined execution. No normality
law for callbacks or nested Wasm calls is an input to this theorem. -/
theorem platform_partial_effects {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (token : Unit) (identity : U64) (args defaults : Slice runtime.Value) :
    (platform memory floats allocator select).call_host token store identity args defaults ⦃answer=>∃afterCode,
      ReentrantCallbacks.Effect view code store afterCode answer.2.2.1 ∧
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value⦄div := by
  have safe := run_safe memory floats allocator correct allocation view laws select code (initialHost select store identity args)
    (initialHost_guard memory view code select store held identity args)
  simp only [platform]
  generalize actual : run memory floats allocator select (initialHost select store identity args)=result at safe ⊢
  cases safe with
  | div => simp only [bind_div]; exact WP.dspec.div _
  | ret post =>
    rename_i answer
    obtain ⟨count,trace,afterCode,effect,fresh⟩ := post
    have kind := initialHost_return_kind memory floats allocator select store identity args trace
    cases answer with
    | invocation answer history => cases kind
    | host answer history =>
      rcases answer with ⟨status,after,values⟩
      simp only [bind_ok]
      exact WP.dspec.ret ⟨afterCode,effect,fresh.2⟩
end Exec.Theorems.OpenReentrantControl
