import Itasca.Results.Definitions
import Itasca.Results.Validate
import Itasca.Results.Stream
import Itasca.Results.Batch
import Itasca.Results.Trace
import Itasca.Results.Unique
import Itasca.Results.Compile
import Itasca.Results.Instantiate
import Itasca.Results.Invoke
import Itasca.Results.Store
import Itasca.Runtime.Platform.VecMemory
import Itasca.Runtime.Platform.FloatWitness
import Itasca.Runtime.Integration.Host.TrapWitness

/-!
# Itasca public interface and results

Validation, compilation and execution share one [semantic interface](Results/Definitions/README.md).
Every public theorem is stated in full in one of the nine Results modules below.
Namespaces, including `Itasca.Runtime.*`, retain their existing names;
public definition ownership is under Interface, and construction proofs remain internal.

## Validation, streaming and traces

[Results/Validate](Results/Validate.lean), whole-module validation:
- `metadata.validate_module.spec`, `total`, `sound`
- `metadata.validate_module.complete`, `complete_with_metadata`

[Results/Stream](Results/Stream.lean), the streaming driver:
- `stream.validate_streaming.sound`, `total`, `complete`

[Results/Batch](Results/Batch.lean), worker batches:
- `stream.CodeBatch.validate_all.spec`, `total`, `complete`
- `stream.CodeBatch.finish.sound`

[Results/Trace](Results/Trace.lean), callback traces:
- `code.validate_body_with.trace`, `trace_sound`, `trace_complete`
- `metadata.validate_code_entry_with.trace_sound`

[Results/Unique](Results/Unique.lean), decoding uniqueness:
- `Binary.module_unique`

[streaming interface](Results/Definitions/Streaming.lean), streaming premises:
- soundness: `Stream.Source.Coherent`, `Stream.Scheduler.Provenance`
- termination: `Stream.Source.CallbacksTotal`, `Stream.Scheduler.CallbacksTotal`
- completeness: `Stream.Source.CanonicalAvailable`, `Stream.Scheduler.Accepts`

## Compilation, store, instantiation and invocation

These results retain explicit platform, host, source-validity and resource premises.
Read [Compilation](Results/Definitions/Compiler/Compilation.lean), [Store](Results/Definitions/Runtime.lean),
[Instantiation](Results/Definitions/Runtime.lean), [Invocation](Results/Definitions/Runtime.lean)
and [Platform](Results/Definitions/Platform.lean) for their vocabulary. Native wrappers remain
outside the kernel proof, and the execution model remains sequential.

[Results/Compile](Results/Compile.lean), compilation:
- `runtime.compiler.compile_with.sound`, `spec`
- `runtime.compiler.compile_with.complete`, `complete_spec`
- `runtime.compiler.compile_default_with.spec`

[Results/Instantiate](Results/Instantiate.lean), instantiation of a compiled module:
- `runtime.store.instantiate.Store.instantiate_with.spec`

[Results/Invoke](Results/Invoke.lean), invocation of an issued function:
- behavior: `runtime.interp.invoke_with.behaves`, `terminates`, `resource_complete`
- resource exhaustion and interruption preserve reachable source effects; resource
  sufficiency is an internal theorem, not a public API premise

[Results/Store](Results/Store.lean) proves `Integration.runtime_verified`, the
existence of the abstract runtime protocol, and its store operations (under `Store`):
- creation: `with_identity.spec`
- definitions: `define_extern_with.spec`, `define_host_with.spec`, `define_memory_with.spec`,
  `define_table_with.spec`, `define_global_with.spec`
- writes and growth: `set_global.spec`, `set_table.spec`, `memory_mut.spec`,
  `grow_memory_with.spec`, `grow_table_with.spec`
- reads: `global.spec`, `memory.spec`, `table_size.spec`, `table_get.spec`,
  `func_type.spec`, `extern_identity.spec`, `export.spec`

[Interface](Results/Definitions/README.md), embedder obligations:
- platform: `Platform.AllocCorrect`, `Platform.AllocationAvailable`, `Platform.FloatOpsCorrect`,
  `Platform.MemoryLaws`
- host callbacks: `HostReturn`, `HostLaws`, `NoHostStackOverflow`
- compiler: `Compiler.ValidCompilationSource`, `Compiler.CompileEligible`
- source execution: SpecTec configurations and SpecExt host-aware reductions
-/
