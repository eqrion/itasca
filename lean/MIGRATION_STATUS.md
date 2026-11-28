# Shared Wasm metadata proof migration

The Lean proofs cover the extracted API that returns `ModuleMetadata<Arc<CodeMetadata>>`. Batches own a strong reference to the code descriptors and borrow their source bytes. After the tail parser decodes the data segments and outstanding batches retire successfully, the streaming driver returns the module with those segments.

## Public guarantees

- Slice and streaming soundness identify the returned module’s declarations, ordered import and export types, data segments, and descriptor flags. The eager function flag corresponds to a start or exported function. The table, memory and global export flags correspond to their respective exports.
- Completeness for both entry points constructs the returned metadata from independently encoded and typed modules within the implementation limits. The streaming theorems retain separate source and scheduler premises for soundness, totality and completeness.
- The batch worker’s `CodeEntry.Bounds` premise includes the bound on imported functions used to index defined functions. The decoded module’s `Module.Environment.Cache.imported_func_bound` supplies it.

The public theorem statements are in [Results/Validate.lean](Itasca/Itasca/Results/Validate.lean), [Results/Stream.lean](Itasca/Itasca/Results/Stream.lean) and [Results/Batch.lean](Itasca/Itasca/Results/Batch.lean).

## Trust boundary and verification

The handwritten model treats construction, cloning and dereferencing of a strong reference as preserving its immutable value. It assumes successful allocation and a representable strong count. Atomic ordering, destruction timing and exhaustion are outside its scope. See the [formal verification guarantees and trust boundary](../README.md#formal-verification).

From `lean/`, run `just extract-check` to compare the generated Rust model, `just prove` to build all proofs and examples, and `just audit` to check their axiom dependencies.
