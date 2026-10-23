import Exec.Theorems.Instantiation.StartEquation
import Exec.Theorems.Invocation.InvokeSupported
import Exec.Theorems.Composition.Certified.CertifiedExecutable
import Exec.Theorems.Instantiation.InstantiateStartSlice
import Exec.Theorems.Instantiation.StartAmbient
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

/-- A checked zero-argument, zero-result start uses the mutable Core invocation
proof and retains all committed store writes. -/
theorem invoke_start_executable_ambient {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedExecutableStore view code store) (hostFree : CoreHostFree store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (args : Slice runtime.Value) (empty : args.val = [])
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (params : signature.params.val = []) (results : signature.results.val = []) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args (alloc.vec.Vec.new runtime.Value)
      ⦃ out =>
        (CertifiedExecutableStore view code out.2.2.1 ∧ Interp.FrameStoreMetadata store out.2.2.1 ∧
          Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1)) ∧
        (out.1 = .Ok () → out.2.2.2.2.val = [] ∧ StepsH (ambientStartConfiguration view code store ambient address) []
          ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,[]⟩) ∧
        (∀ error, out.1 = .Err error → SupportedInvocationError (ambientStartConfiguration view code store ambient address)
          (Store.decodeStore view code out.2.2.1) ambient error) ⦄div := by
  obtain ⟨instanceIndex,functionIndex,wasm⟩ : ∃ ii fi, function.code = .Wasm ii fi := by
    cases kind : function.code with
    | Host host => exact False.elim (hostFree function (List.mem_of_getElem? hf) host kind)
    | Wasm ii fi => exact ⟨ii,fi,rfl⟩
  have checked := Interp.typed_arguments_accepted memory store (Store.decodeStore view code store)
    args signature.params (by simp [ResultsTyped,params,empty]) (by simp [empty])
  apply WP.dspec_mono (invoke_defined_supported_outcomes Abs.executable_language memory hooks floats allocator correct allocation interrupts
    view laws code exec store platform certified hostFree ambient ambientWf address function signature
    instanceIndex functionIndex args (alloc.vec.Vec.new runtime.Value) owner (by simp [empty]) hf hs wasm checked)
  intro out outcome
  refine ⟨⟨outcome.1.1,outcome.1.2.1,outcome.1.2.2.1⟩,?_,?_⟩
  · intro success
    obtain ⟨tags,steps⟩ := outcome.2.1 success
    have noValues : out.2.2.2.2.val = [] := by
      simpa only [results,List.map_nil,List.nil_eq,List.map_eq_nil_iff] using tags
    exact ⟨noValues,by simpa [ambientStartConfiguration,empty,noValues,vals] using steps⟩
  · intro error rejected
    simpa [ambientStartConfiguration,empty,vals] using outcome.2.2 error rejected

/-- The actual instantiation-start wrapper propagates Core results and traps
with the final certified store and the committed-publication flag. -/
theorem instantiate_start_executable_ambient {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedExecutableStore view code store) (hostFree : CoreHostFree store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (identity : runtime.InstanceAddr) (address : runtime.FuncAddr)
    (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (params : signature.params.val = []) (results : signature.results.val = []) :
    Store.instantiate_start memory hooks floats allocator identity address store platform
      ⦃ out => out.2.2.2 = true ∧
        (CertifiedExecutableStore view code out.2.1 ∧ Interp.FrameStoreMetadata store out.2.1 ∧
          Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.1)) ∧
        (∀ returned, out.1 = .Ok returned → returned = identity ∧
          StepsH (ambientStartConfiguration view code store ambient address) []
            ⟨⟨Store.decodeStore view code out.2.1,ambient⟩,[]⟩) ∧
        (∀ error, out.1 = .Err error → SupportedInvocationError (ambientStartConfiguration view code store ambient address)
          (Store.decodeStore view code out.2.1) ambient error) ⦄div := by
  rw [start_equation]
  apply WP.dspec_bind (invoke_start_executable_ambient memory hooks floats allocator correct allocation interrupts view laws code
    startExecution store platform certified hostFree ambient ambientWf address function signature startArguments rfl owner hf hs params results)
  rintro ⟨status,execution,after,host,values⟩ ⟨retained,success,errors⟩
  cases status with
  | Ok unitValue =>
    apply WP.dspec.ret
    refine ⟨rfl,retained,?_,?_⟩
    · intro returned same
      cases same
      exact ⟨rfl,(success rfl).2⟩
    · intro error impossible; cases impossible
  | Err error =>
    apply WP.dspec.ret
    refine ⟨rfl,retained,?_,?_⟩
    · intro returned impossible; cases impossible
    · intro other same
      cases same
      exact errors error rfl
end Exec.Theorems
