import Exec.Contracts
import Exec.Results.Compile
import Exec.Results.Instantiate
import Exec.Results.Invoke

/-!
# Execution results

The public guarantees of the slot runtime. Every headline theorem is stated in full in one of the
files below; everything else in the library supports them. `profile_*` theorems quantify over both
complete `ValidationProfile` values. The obligations the results place on an embedding (platform
operations, host callbacks, compiler eligibility and source resources) are listed in
[Contracts](Contracts.lean).

[Results/Compile](Results/Compile.lean), compilation:
- `runtime.compiler.compile_with.profile_sound`, `profile_spec`
- `runtime.compiler.compile_with.profile_complete`, `profile_complete_spec`
- `runtime.compiler.compile_default_with.profile_spec`

[Results/Instantiate](Results/Instantiate.lean), instantiation of a compiled module:
- `runtime.store.instantiate.Store.instantiate_with.spec`

[Results/Invoke](Results/Invoke.lean), invocation of an issued function:
- behavior: `runtime.interp.invoke_with.behaves`, `terminates`
- completeness: `runtime.interp.invoke_with.no_spurious_errors`

[Contracts](Contracts.lean), embedder obligations:
- platform: `Platform.AllocCorrect`, `Platform.AllocationAvailable`, `Platform.FloatOpsCorrect`,
  `Platform.MemoryLaws`
- host callbacks: `HostWorldSound`, `NoHostStackOverflow`
- compiler: `Code.ValidCompilationSource`, `Code.CompileEligible`
- source resources: `SourceResourcesFit`, `Interp.SourceCanonicalFunctionCapacity`
-/
