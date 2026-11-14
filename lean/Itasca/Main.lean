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
import Itasca.Results.Store

/-!
# Validator results

The public guarantees of the validator. Every headline theorem is stated in full in one of the
files below; everything else in the library supports them. The embedding
obligations of the streaming results are defined in [Contracts](Contracts.lean).

[Results/Validate](Results/Validate.lean), whole-module validation:
- `metadata.validate_module.spec`, `total`, `sound`
- `metadata.validate_module.complete`, `complete_with_metadata`

[Results/Stream](Results/Stream.lean), the streaming driver:
- `stream.validate_streaming.sound`, `total`, `complete`

[Results/Batch](Results/Batch.lean), worker batches:
- `stream.CodeBatch.validate_func.total`, `complete`
- `stream.CodeBatch.validate_all.spec`, `total`, `complete`, `complete_seed`
- `stream.CodeBatch.finish.sound`

[Results/Trace](Results/Trace.lean), callback traces:
- `code.validate_body_with.trace`, `trace_sound`, `trace_complete`, `instrument_trace`,
  `recorder_total`, `recorder_complete`
- `metadata.validate_code_entry_with.trace_sound`

[Results/Unique](Results/Unique.lean), decoding uniqueness:
- `Profile.module_unique`

[Contracts](Contracts.lean), streaming premises:
- soundness: `StreamSource.Coherent`, `StreamScheduler.Provenance`
- termination: `StreamSource.CallbacksTotal`, `StreamScheduler.CallbacksTotal`
- completeness: `StreamSource.CanonicalAvailable`, `StreamAcceptingScheduler.Accepts`

# Runtime results

The public guarantees of the slot runtime. Every headline theorem is stated in full in one of the
files below; everything else in the library supports them. The obligations the results place on an embedding (platform
operations, host callbacks, compiler eligibility and source resources) are listed in
[Runtime/Contracts](Runtime/Contracts.lean).

[Results/Compile](Results/Compile.lean), compilation:
- `runtime.compiler.compile_with.sound`, `spec`
- `runtime.compiler.compile_with.complete`, `complete_spec`
- `runtime.compiler.compile_default_with.spec`

[Results/Instantiate](Results/Instantiate.lean), instantiation of a compiled module:
- `runtime.store.instantiate.Store.instantiate_with.spec`

[Results/Invoke](Results/Invoke.lean), invocation of an issued function:
- behavior: `runtime.interp.invoke_with.behaves`, `terminates`
- completeness: `runtime.interp.invoke_with.no_spurious_errors`

[Results/Store](Results/Store.lean), store operations (all names under `runtime.store.Store`):
- creation: `with_identity.spec`
- definitions: `define_extern_with.spec`, `define_host_with.spec`, `define_memory_with.spec`,
  `define_table_with.spec`, `define_global_with.spec`
- writes and growth: `set_global.spec`, `set_table.spec`, `memory_mut.spec`,
  `grow_memory_with.spec`, `grow_table_with.spec`
- reads: `global.spec`, `memory.spec`, `table_size.spec`, `table_get.spec`,
  `func_type.spec`, `extern_identity.spec`, `export.spec`

[Runtime/Contracts](Runtime/Contracts.lean), embedder obligations:
- platform: `Platform.AllocCorrect`, `Platform.AllocationAvailable`, `Platform.FloatOpsCorrect`,
  `Platform.MemoryLaws`
- host callbacks: `HostWorldSound`, `NoHostStackOverflow`
- compiler: `Compiler.ValidCompilationSource`, `Compiler.CompileEligible`
- source resources: `SourceResourcesFit`, `Interp.SourceCanonicalFunctionCapacity`
-/
