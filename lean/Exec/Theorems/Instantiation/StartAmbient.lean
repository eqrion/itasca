import Exec.Theorems.Composition.Certified.CertifiedSlice
import Exec.Theorems.Invocation.InvokeSliceTypedOutcomes
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

def ambientStartConfiguration {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (ambient : frame) (address : runtime.FuncAddr) : config :=
  ⟨⟨Store.decodeStore view code store, ambient⟩, [.CALL_ADDR address.index.val]⟩

/-- The checked empty start signature returns no values. This retains the
result-type fact supplied by actual slot readback. -/
theorem invoke_start_slice_ambient {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedSliceStore view code store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.Function) (signature : Itasca.types.FuncType)
    (args : Slice runtime.Value) (empty : args.val = [])
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (params : signature.params.val = []) (results : signature.results.val = []) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args (alloc.vec.Vec.new runtime.Value)
      ⦃ out => out.2.2.1 = store ∧
        (out.1 = .Ok () → out.2.2.2.2.val = [] ∧ StepsH (ambientStartConfiguration view code store ambient address) []
          ⟨⟨Store.decodeStore view code store, ambient⟩, []⟩) ∧
        (∀ error, out.1 = .Err error → SliceInvocationError (ambientStartConfiguration view code store ambient address)
          (Store.decodeStore view code store) ambient error) ⦄div := by
  obtain ⟨instanceIndex, functionIndex, inst, compiled, functions, declared, body, epilogue,
    wasm, hi, hc, sourceCode, table, certificate⟩ := certified.resolve address function signature hf hs
  have checked := Interp.typed_arguments_accepted memory store (Store.decodeStore view code store)
    args signature.params (by simp [ResultsTyped, params, empty]) (by simp [empty])
  have invocation := invoke_defined_slice_typed_outcomes memory hooks floats allocator allocation interrupts
    view code exec store platform certified.shape certified.storeSyntax certified.typed certified.slice
    ambient ambientWf address function signature instanceIndex functionIndex inst compiled
    functions declared body epilogue args (alloc.vec.Vec.new runtime.Value) owner certified.compiled
    (by simp [results]) (by simp [empty]) certificate table hf hs wasm hi hc sourceCode checked
  apply WP.dspec_mono invocation
  intro out outcome
  refine ⟨outcome.1, ?_, ?_⟩
  · intro ok
    obtain ⟨tags, steps⟩ := outcome.2.1 ok
    have noValues : out.2.2.2.2.val = [] := by
      simpa only [results, List.map_nil, List.nil_eq, List.map_eq_nil_iff] using tags
    exact ⟨noValues, by simpa [ambientStartConfiguration, empty, noValues, vals] using steps⟩
  · intro error rejected
    simpa [ambientStartConfiguration, empty, vals] using outcome.2.2 error rejected

theorem invoke_start_slice_ambient_divergence {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedSliceStore view code store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.Function) (signature : Itasca.types.FuncType)
    (args : Slice runtime.Value) (empty : args.val = [])
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (params : signature.params.val = []) (results : signature.results.val = [])
    (divergent : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args (alloc.vec.Vec.new runtime.Value) = .div)
    (requested : Nat) :
    ∃ final count, Spec.StepsHN count (ambientStartConfiguration view code store ambient address) [] final ∧ requested ≤ count := by
  obtain ⟨instanceIndex, functionIndex, inst, compiled, functions, declared, body, epilogue,
    wasm, hi, hc, sourceCode, table, certificate⟩ := certified.resolve address function signature hf hs
  simpa [ambientStartConfiguration, empty, vals] using
    invoke_defined_slice_no_silent_divergence memory hooks floats allocator allocation interrupts
      view code exec store platform certified.shape certified.storeSyntax certified.typed certified.slice
      ambient ambientWf address function signature instanceIndex functionIndex inst compiled
      functions declared body epilogue args (alloc.vec.Vec.new runtime.Value) owner certified.compiled
      (by simp [results]) (by simp [empty]) certificate table hf hs wasm hi hc sourceCode divergent requested
end Exec.Theorems
