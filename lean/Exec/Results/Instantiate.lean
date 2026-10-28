import Exec.Theorems.Instantiation.InstantiateSource

/-!
# Instantiation

Guarantees of `runtime.store.instantiate.Store.instantiate_with` for a module accepted by
`runtime.compiler.compile_with`, with issued imports, from a store in the public invariant
`Theorems.ExecutableInv`. Instantiation links, allocates and initializes the module and returns
its start function without running it, so it uses no host callback, interrupt or float operation.
The caller invokes the start function with `runtime.interp.invoke_with`.
-/

open Aeneas Aeneas.Std SpecExt

namespace Itasca.Runtime

open Itasca Theorems Store

/-- Actual accepted compilation and public instantiation terminate. The final code
interpretation installs the module's source functions at the next instance index. The full
invariant, raw prefix and cross-world source extension use that interpretation.
`InstantiationSourceOutcome` separates failure before publication, which rolls back, from
initialization after publication, which reaches the call of the returned start function or a trap.
`InstantiationResourceCause` classifies every resource error. The module is also source-typed. -/
theorem runtime.store.instantiate.Store.instantiate_with.spec {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (oldCode : CodeInterpretation) (old : ExecutableInv view oldCode before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (bytes : Slice U8) (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module))
    (raw : ModuleBinary.Module)
    (encoded : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile) :
    Module_ok (ModuleElaboration.moduleOf raw) ∧
      runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
        ⦃ out => ExecutableInv view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) out.2.1 ∧
          Interp.FrameStorePrefix before out.2.1 ∧
          Extend_store (decodeStore view oldCode before)
            (decodeStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) out.2.1) ∧
          InstantiationSourceOutcome view oldCode (installCode oldCode before.instances.length (Code.sourceFunctions raw))
            before module imports raw platform out.1 out.2.1 out.2.2 ∧
          ∀ error, out.1 = .Err error → InstantiationResourceCause memory hooks floats allocator
            view oldCode before module imports platform raw out.2.1 error ⦄ :=
  instantiate_compiled_source memory hooks floats allocator view laws law before module imports platform
    oldCode old handles bytes profile limits accepted raw encoded

end Itasca.Runtime
