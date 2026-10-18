import Exec.Theorems.Instantiation.StartEquation
import Exec.Theorems.Instantiation.StartInvocation
import Exec.Store.Instantiation.InstantiateStart
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

/-- Starting a certified slice function uses the real fresh-execution wrapper.
Every normal outcome retains the committed store; start traps and interruption
are propagated unchanged, and successful starts finish with no source values. -/
theorem instantiate_start_slice {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedSliceStore view code store)
    (identity : runtime.InstanceAddr) (address : runtime.FuncAddr)
    (function : runtime.store.Function) (signature : Itasca.types.FuncType)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (params : signature.params.val = []) (results : signature.results.val = []) :
    Store.instantiate_start memory hooks floats allocator identity address store platform
      ⦃ out => out.2.1 = store ∧ out.2.2.2 = true ∧ CertifiedSliceStore view code out.2.1 ∧
        (∀ returned, out.1 = .Ok returned → returned = identity ∧
          StepsH (startConfiguration view code store address) []
            ⟨⟨Store.decodeStore view code store, Spec.invocationFrame⟩, []⟩) ∧
        (∀ error, out.1 = .Err error → SliceInvocationError (startConfiguration view code store address)
          (Store.decodeStore view code store) Spec.invocationFrame error) ⦄div := by
  rw [start_equation]
  apply WP.dspec_bind (invoke_start_slice memory hooks floats allocator allocation interrupts view code
    startExecution store platform certified address function signature startArguments rfl owner hf hs params results)
  rintro ⟨status, execution, after, host, values⟩ ⟨unchanged, success, errors⟩
  dsimp only at unchanged success errors
  subst after
  cases status with
  | Ok unitValue =>
    apply WP.dspec.ret
    refine ⟨rfl, rfl, certified, ?_, ?_⟩
    · intro returned same
      cases same
      exact ⟨rfl, (success rfl).2⟩
    · intro error impossible; cases impossible
  | Err error =>
    apply WP.dspec.ret
    refine ⟨rfl, rfl, certified, ?_, ?_⟩
    · intro returned impossible; cases impossible
    · intro other same
      cases same
      exact errors error rfl

/-- A divergent start cannot be a silent wrapper failure: its source invocation
admits executions of every requested finite length. -/
theorem instantiate_start_slice_divergence {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedSliceStore view code store)
    (identity : runtime.InstanceAddr) (address : runtime.FuncAddr)
    (function : runtime.store.Function) (signature : Itasca.types.FuncType)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (params : signature.params.val = []) (results : signature.results.val = [])
    (divergent : Store.instantiate_start memory hooks floats allocator identity address store platform = .div)
    (requested : Nat) :
    ∃ final count, Spec.StepsHN count (startConfiguration view code store address) [] final ∧ requested ≤ count := by
  have checked := invoke_start_slice memory hooks floats allocator allocation interrupts view code
    startExecution store platform certified address function signature startArguments rfl owner hf hs params results
  rw [start_equation] at divergent
  generalize runEq : runtime.interp.invoke_with memory hooks floats allocator startExecution store platform
    address startArguments (alloc.vec.Vec.new runtime.Value) = run at checked divergent
  cases checked with
  | @ret post out outcome =>
    obtain ⟨status, execution, after, host, values⟩ := out
    simp only [bind_ok] at divergent
    cases status <;> simp at divergent
  | div =>
    exact invoke_certified_slice_divergence memory hooks floats allocator allocation interrupts view code
      startExecution store platform certified address function signature startArguments (alloc.vec.Vec.new runtime.Value)
      owner hf hs (by change ∀ value ∈ ([] : List runtime.Value), _; simp) (by simp [results]) (startConfiguration view code store address)
      (certified_start_invocation view code store certified address function signature hf hs params results)
      runEq requested
end Exec.Theorems
