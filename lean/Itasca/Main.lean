import Itasca.Contracts
import Itasca.Results.Validate
import Itasca.Results.Stream
import Itasca.Results.Batch
import Itasca.Results.Trace
import Itasca.Results.Unique
import Itasca.Runtime.Contracts
import Itasca.Results.Compile
import Itasca.Results.Instantiate
import Itasca.Results.Invoke

/-!
# Validator results

The public guarantees of the validator. Every headline theorem is stated in full in one of the
files below; everything else in the library supports them. `profile_*` theorems quantify over both
`ValidationProfile` values, and `wasm_*` corollaries specialize to Wasm 1.0. The embedding
obligations of the streaming results are defined in [Contracts](Contracts.lean).

[Results/Validate](Results/Validate.lean), whole-module validation:
- `module.validate_module.profile_spec`, `profile_total`, `profile_sound`
- `module.validate_module.profile_complete`, `profile_complete_with_metadata`
- `module.validate_module.wasm_spec`, `wasm_total`, `wasm_sound`, `wasm_complete`,
  `wasm_complete_with_metadata`

[Results/Stream](Results/Stream.lean), the streaming driver:
- `stream.validate_streaming.profile_sound`, `profile_total`, `profile_complete`
- `stream.validate_streaming.wasm_sound`, `wasm_total`, `wasm_complete`

[Results/Batch](Results/Batch.lean), worker batches:
- `stream.CodeBatch.validate_func.total`, `complete`
- `stream.CodeBatch.validate_all.spec`, `total`, `complete`, `complete_seed`
- `stream.CodeBatch.finish.sound`

[Results/Trace](Results/Trace.lean), callback traces:
- `code.validate_body_with.trace`, `trace_sound`, `trace_complete`, `instrument_trace`,
  `recorder_total`, `recorder_complete`
- `module.validate_code_entry_with.trace_sound`

[Results/Unique](Results/Unique.lean), decoding uniqueness:
- `Profile.module_unique`, `ModuleBinary.ModuleEncoding.unique`

[Contracts](Contracts.lean), streaming premises:
- soundness: `StreamSource.Coherent`, `StreamScheduler.Provenance`
- termination: `StreamSource.CallbacksTotal`, `StreamScheduler.CallbacksTotal`
- completeness: `StreamSource.CanonicalAvailable`, `StreamAcceptingScheduler.Accepts`

# Runtime results

The public guarantees of the slot runtime. Every headline theorem is stated in full in one of the
files below; everything else in the library supports them. `profile_*` theorems quantify over both
complete `ValidationProfile` values. The obligations the results place on an embedding (platform
operations, host callbacks, compiler eligibility and source resources) are listed in
[Runtime/Contracts](Runtime/Contracts.lean).

[Results/Compile](Results/Compile.lean), compilation:
- `runtime.compiler.compile_with.profile_sound`, `profile_spec`
- `runtime.compiler.compile_with.profile_complete`, `profile_complete_spec`
- `runtime.compiler.compile_default_with.profile_spec`

[Results/Instantiate](Results/Instantiate.lean), instantiation of a compiled module:
- `runtime.store.instantiate.Store.instantiate_with.spec`

[Results/Invoke](Results/Invoke.lean), invocation of an issued function:
- behavior: `runtime.interp.invoke_with.behaves`, `terminates`
- completeness: `runtime.interp.invoke_with.no_spurious_errors`

[Runtime/Contracts](Runtime/Contracts.lean), embedder obligations:
- platform: `Platform.AllocCorrect`, `Platform.AllocationAvailable`, `Platform.FloatOpsCorrect`,
  `Platform.MemoryLaws`
- host callbacks: `HostWorldSound`, `NoHostStackOverflow`
- compiler: `Compiler.ValidCompilationSource`, `Compiler.CompileEligible`
- source resources: `SourceResourcesFit`, `Interp.SourceCanonicalFunctionCapacity`
-/
