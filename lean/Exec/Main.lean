import Exec.Contracts
import Exec.Results.Compile
import Exec.Results.Instantiate
import Exec.Results.Invoke
import Exec.Results.Host

/-!
# Execution results

The public guarantees of the slot runtime. Every headline theorem is stated in full in one of the
files below; everything else in the library supports them. `profile_*` theorems quantify over both
complete `ValidationProfile` values. The obligations the results place on an embedding (platform
operations, host callbacks, compiler eligibility and chosen-run compatibility) are listed in
[Contracts](Contracts.lean).

[Results/Compile](Results/Compile.lean), compilation:
- `runtime.compiler.compile_with.profile_sound`, `profile_spec`
- `runtime.compiler.compile_with.profile_complete`, `profile_complete_spec`
- `runtime.compiler.compile_default_with.profile_spec`

[Results/Instantiate](Results/Instantiate.lean), instantiation of a compiled module:
- `runtime.store.instantiate.Store.instantiate_with.sound`, `recorded_sound`

[Results/Invoke](Results/Invoke.lean), invocation of an issued function:
- soundness: `runtime.interp.invoke_with.sound`, `recorded_sound`, `recorder_sound`
- divergence: `runtime.interp.invoke_with.diverges`, `terminates`
- progress: `runtime.interp.invoke_with.finite_progress`
- completeness: `runtime.interp.invoke_with.chosen_complete`

[Results/Host](Results/Host.lean), the certified synchronous host driver:
- `Theorems.OpenReentrantControl.invoke.chosen_complete`
- `Theorems.OpenReentrantControl.platform.invoke_chosen_complete`, `invoke_chosen_sound`,
  `invoke_chosen_diverges`, `invoke_chosen_terminates`
- `Theorems.OpenReentrantControl.platform.returning_call_host`, `returning_package`,
  `invoke_returning_terminates`

[Contracts](Contracts.lean), embedder obligations:
- platform: `Platform.AllocCorrect`, `Platform.AllocationAvailable`, `Platform.FloatOpsCorrect`,
  `Platform.MemoryLaws`
- host callbacks: `HostWorldSound`, `WorldInvocationLaws`, `HostWorldChosenSound`,
  `NoHostStackOverflow`
- compiler: `Code.ValidCompilationSource`, `Code.CompileEligible`
- chosen runs: `Spec.SourceChoices.Admissible`, `GrowthChoicesCompatible`, `ChosenWorldResources`,
  and the host-driver choice contracts
-/
