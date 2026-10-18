import Exec.Theorems.Invocation.PublicExecutableInvocation
import Exec.Theorems.Api.CertifiedApiMetadata

namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem invoke_executable_api_issued {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedExecutableApiStore view code store) (hostFree : CoreHostFree store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀ value ∈ args.val, Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => CertifiedExecutableApiStore view code out.2.2.1 ∧
        ExecutableInvocationOutcome view code store exec platform results initial out ⦄div := by
  apply WP.dspec_mono (invoke_executable_issued memory hooks floats allocator correct allocation interrupts
    view laws code exec store platform certified.toCertifiedSupportedStore hostFree address args results
    issued argumentIssued initial invoked)
  intro out outcome
  exact ⟨certified.frame_metadata outcome.1 outcome.2.1,outcome⟩

end Exec.Theorems
