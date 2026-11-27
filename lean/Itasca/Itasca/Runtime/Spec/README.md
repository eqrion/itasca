# Source facts for execution

[Primitive operations](PrimitiveOperations.lean), [SIMD](Simd/), and [bulk operations](BulkOperations.lean) establish facts directly about the generated Wasm rules and patched builtins. This is the place for a lemma about a source result, memory bound, or segment effect whose premises can be stated independently of any compiled code or interpreter run.
