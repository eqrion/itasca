import Exec.Theorems.Instantiation.StartEquation
import Exec.Theorems.Instantiation.InstantiateStartSlice
import Exec.Theorems.Instantiation.StartAmbient
import Exec.Store.Instantiation.InstantiateStart
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

/-- Starting a certified slice function uses the real fresh-execution wrapper.
Every normal outcome retains the committed store; start traps and interruption
are propagated unchanged, and successful starts finish with no source values. -/
theorem instantiate_start_slice_ambient {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedSliceStore view code store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (identity : runtime.InstanceAddr) (address : runtime.FuncAddr)
    (function : runtime.store.Function) (signature : Itasca.types.FuncType)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (params : signature.params.val = []) (results : signature.results.val = []) :
    Store.instantiate_start memory hooks floats allocator identity address store platform
      ⦃ out => out.2.1 = store ∧ out.2.2.2 = true ∧ CertifiedSliceStore view code out.2.1 ∧
        (∀ returned, out.1 = .Ok returned → returned = identity ∧
          StepsH (ambientStartConfiguration view code store ambient address) []
            ⟨⟨Store.decodeStore view code store, ambient⟩, []⟩) ∧
        (∀ error, out.1 = .Err error → SliceInvocationError (ambientStartConfiguration view code store ambient address)
          (Store.decodeStore view code store) ambient error) ⦄div := by
  rw [start_equation]
  apply WP.dspec_bind (invoke_start_slice_ambient memory hooks floats allocator allocation interrupts view code
    startExecution store platform certified ambient ambientWf address function signature startArguments rfl owner hf hs params results)
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
theorem instantiate_start_slice_ambient_divergence {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedSliceStore view code store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (identity : runtime.InstanceAddr) (address : runtime.FuncAddr)
    (function : runtime.store.Function) (signature : Itasca.types.FuncType)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (params : signature.params.val = []) (results : signature.results.val = [])
    (divergent : Store.instantiate_start memory hooks floats allocator identity address store platform = .div)
    (requested : Nat) :
    ∃ final count, Spec.StepsHN count (ambientStartConfiguration view code store ambient address) [] final ∧ requested ≤ count := by
  have checked := invoke_start_slice_ambient memory hooks floats allocator allocation interrupts view code
    startExecution store platform certified ambient ambientWf address function signature startArguments rfl owner hf hs params results
  rw [start_equation] at divergent
  generalize runEq : runtime.interp.invoke_with memory hooks floats allocator startExecution store platform
    address startArguments (alloc.vec.Vec.new runtime.Value) = run at checked divergent
  cases checked with
  | @ret post out outcome =>
    obtain ⟨status, execution, after, host, values⟩ := out
    simp only [bind_ok] at divergent
    cases status <;> simp at divergent
  | div =>
    exact invoke_start_slice_ambient_divergence memory hooks floats allocator allocation interrupts view code
      startExecution store platform certified ambient ambientWf address function signature startArguments rfl
      owner hf hs params results runEq requested
end Exec.Theorems
