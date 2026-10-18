import Exec.Theorems.Instantiation.StartEquation
import Exec.Theorems.Instantiation.StartExecutableResolved
import Exec.Theorems.Invocation.InvokeSupported
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

theorem invoke_start_executable_segments {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedExecutableStore view code store) (hostFree : CoreHostFree store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.Function) (signature : Itasca.types.FuncType)
    (args : Slice runtime.Value) (empty : args.val = [])
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (params : signature.params.val = []) (results : signature.results.val = []) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args (alloc.vec.Vec.new runtime.Value)
      ⦃ out => Store.SegmentCounts store out.2.2.1 ⦄div := by
  obtain ⟨instanceIndex,functionIndex,wasm⟩ : ∃ ii fi, function.code = .Wasm ii fi := by
    cases kind : function.code with
    | Host host => exact False.elim (hostFree function (List.mem_of_getElem? hf) host kind)
    | Wasm ii fi => exact ⟨ii,fi,rfl⟩
  have checked := Interp.typed_arguments_accepted memory store (Store.decodeStore view code store)
    args signature.params (by simp [ResultsTyped,params,empty]) (by simp [empty])
  apply WP.dspec_mono (invoke_defined_supported_outcomes Abs.executable_language memory hooks floats allocator correct allocation interrupts
    view laws code exec store platform certified hostFree ambient ambientWf address function signature instanceIndex functionIndex
    args (alloc.vec.Vec.new runtime.Value) owner (by simp [empty]) hf hs wasm checked)
  intro out post
  exact post.1.2.2.2

theorem instantiate_start_executable_segments {M P F A : Type}
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
    (function : runtime.store.Function) (signature : Itasca.types.FuncType)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (params : signature.params.val = []) (results : signature.results.val = []) :
    Store.instantiate_start memory hooks floats allocator identity address store platform
      ⦃ out => Store.SegmentCounts store out.2.1 ⦄div := by
  rw [start_equation]
  apply WP.dspec_bind (invoke_start_executable_segments memory hooks floats allocator correct allocation interrupts view laws code
    startExecution store platform certified hostFree ambient ambientWf address function signature startArguments rfl owner hf hs params results)
  rintro ⟨status,execution,after,host,values⟩ reachable
  cases status <;> exact WP.dspec.ret reachable


end Exec.Theorems
