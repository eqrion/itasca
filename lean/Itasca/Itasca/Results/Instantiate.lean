import Itasca.Results.Definitions.Runtime
import Itasca.Runtime.Integration.RuntimeContract

open Itasca.Representation

/-!
# Instantiation

Guarantees of `runtime.store.instantiate.Store.instantiate_with` for a module accepted by
`runtime.compiler.compile_with`, with issued imports, from a store satisfying
the chosen `Inv` predicate. Instantiation links, allocates and initializes the module and returns
its start function without running it, so it uses no host callback, interrupt or float operation.
The caller invokes the start function with `runtime.interp.invoke_with`.
-/

open Aeneas Aeneas.Std WebAssembly

namespace Itasca

open Itasca Integration Store

/-- Actual accepted compilation and public instantiation terminate. The final code
interpretation installs the module's source functions at the next instance index. The full
invariant, raw prefix and cross-world source extension use that interpretation.
`InstantiationSourceOutcome` separates failure before publication, which rolls back, from
initialization after publication, which reaches the call of the returned start function or a trap.
Resource failures are permitted; the module is also source-typed. -/
theorem Store.Instantantiation.instantiate_with.spec {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop)
    (contract : InstantiationContract view Inv)
    (memory_laws : Platform.MemoryLaws memory view)
    (allocator_correct : Platform.AllocCorrect allocator)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (oldCode : CodeInterpretation) (store_invariant : Inv oldCode before)
    (imports_issued : ∀ external ∈ imports.val, ExternalIssued before external)
    (bytes : Slice U8) (limits : runtime.compiler.CompileLimits)
    (compilation_accepted : runtime.compiler.compile_with allocator bytes limits = .ok (.Ok module))
    (raw : Binary.Module)
    (source_encoding : WebAssembly.Binary.ModuleEncoding (Binary.Source.rawModule raw) (Binary.Source.bytes bytes.val)) :
    Module_ok (Module.Elaboration.moduleOf raw) ∧
      runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
        ⦃ (result, after, nextPlatform) => Inv (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) after ∧
          Store.MetadataExtended before after ∧
          Extend_store (decodeStore view oldCode before)
            (decodeStore view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) after) ∧
          InstantiationSourceOutcome view oldCode (installCode oldCode before.instances.length (Compiler.sourceFunctions raw))
            before module imports raw platform result after nextPlatform ⦄ :=
  contract.instantiate memory hooks floats allocator memory_laws allocator_correct before module imports platform oldCode store_invariant imports_issued bytes limits compilation_accepted raw source_encoding

end Itasca
