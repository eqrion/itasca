import Exec.Theorems.Composition.Certified.CertifiedSlice
import Exec.Theorems.Invocation.InvokeSliceTypedOutcomes
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

def startConfiguration {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (address : runtime.FuncAddr) : config :=
  ⟨⟨Store.decodeStore view code store, Spec.invocationFrame⟩, [.CALL_ADDR address.index.val]⟩

theorem start_frame_wf : wf_frame Spec.invocationFrame := by
  constructor
  · simp [Forall]
  · constructor; simp [Forall]

theorem certified_start_invocation {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (certified : CertifiedSliceStore view code store)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (found : store.funcs.val[address.index.val]? = some function)
    (typed : store.types.val[function.signature.val]? = some signature)
    (params : signature.params.val = []) (results : signature.results.val = []) :
    fun_invoke (Store.decodeStore view code store) address.index.val [] (startConfiguration view code store address) := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have sourceBound : address.index.val < (Store.decodeStore view code store).FUNCS.length := by
    simpa [Store.decodeStore] using bound
  have functionType : (Store.decodeFunction code store function).TYPE = .mk_functype (.mk_list []) (.mk_list []) := by
    unfold Store.decodeFunction
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, typed, Option.map_some, Option.getD_some]
    cases function.code with
    | Host id => simp [Store.decodeFuncType, params, results]
    | Wasm instanceIndex functionIndex =>
      dsimp only
      split <;> simp [Store.decodeFuncType, params, results]
  have sourceType : ((Store.decodeStore view code store).FUNCS[address.index.val]!).TYPE =
      .mk_functype (.mk_list []) (.mk_list []) := by
    rw [getElem!_pos (Store.decodeStore view code store).FUNCS address.index.val sourceBound]
    simp only [Store.decodeStore, List.getElem_map]
    rw [(List.getElem?_eq_some_iff.mp found).2]
    exact functionType
  have wfState : wf_state ⟨Store.decodeStore view code store, Spec.invocationFrame⟩ :=
    .state_case_0 _ _ (Store.decodeStore_wf view code store certified.shape certified.storeSyntax) start_frame_wf
  apply fun_invoke.fun_invoke_case_0 _ _ 0 [] Spec.invocationFrame [] [] rfl
  · exact sourceBound
  · exact sourceType
  · constructor
    · exact wfState
    · intro instruction member
      have same : instruction = .CALL_ADDR address.index.val := by simpa [Map] using member
      rw [same]
      exact .admininstr_case_70 _
  · exact start_frame_wf
  · exact wfState
  · rfl

/-- The checked empty start signature returns no values. This retains the
result-type fact supplied by actual slot readback. -/
theorem invoke_start_slice {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedSliceStore view code store)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (args : Slice runtime.Value) (empty : args.val = [])
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (params : signature.params.val = []) (results : signature.results.val = []) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args (alloc.vec.Vec.new runtime.Value)
      ⦃ out => out.2.2.1 = store ∧
        (out.1 = .Ok () → out.2.2.2.2.val = [] ∧ StepsH (startConfiguration view code store address) []
          ⟨⟨Store.decodeStore view code store, Spec.invocationFrame⟩, []⟩) ∧
        (∀ error, out.1 = .Err error → SliceInvocationError (startConfiguration view code store address)
          (Store.decodeStore view code store) Spec.invocationFrame error) ⦄div := by
  obtain ⟨instanceIndex, functionIndex, inst, compiled, functions, declared, body, epilogue,
    wasm, hi, hc, sourceCode, table, certificate⟩ := certified.resolve address function signature hf hs
  have checked := Interp.typed_arguments_accepted memory store (Store.decodeStore view code store)
    args signature.params (by simp [ResultsTyped, params, empty]) (by simp [empty])
  have invocation := invoke_defined_slice_typed_outcomes memory hooks floats allocator allocation interrupts
    view code exec store platform certified.shape certified.storeSyntax certified.typed certified.slice
    Spec.invocationFrame start_frame_wf address function signature instanceIndex functionIndex inst compiled
    functions declared body epilogue args (alloc.vec.Vec.new runtime.Value) owner certified.compiled
    (by simp [results]) (by simp [empty]) certificate table hf hs wasm hi hc sourceCode checked
  apply WP.dspec_mono invocation
  intro out outcome
  refine ⟨outcome.1, ?_, ?_⟩
  · intro ok
    obtain ⟨tags, steps⟩ := outcome.2.1 ok
    have noValues : out.2.2.2.2.val = [] := by
      simpa only [results, List.map_nil, List.nil_eq, List.map_eq_nil_iff] using tags
    exact ⟨noValues, by simpa [startConfiguration, empty, noValues, vals] using steps⟩
  · intro error rejected
    simpa [startConfiguration, empty, vals] using outcome.2.2 error rejected
end Exec.Theorems
