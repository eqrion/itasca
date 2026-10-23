import Exec.Theorems.Instantiation.InstantiateExecutableWorldSource
import Exec.Theorems.Instantiation.InstantiateExecutableWorldRecordingResources

/-!
# Instantiation

Guarantees of `runtime.store.instantiate.Store.instantiate_with` for a module accepted by
`runtime.compiler.compile_with`, with issued imports, from a store in the public invariant
`Theorems.ExecutableInv`. Start callbacks may publish fresh code.

The premises are the platform and host laws of [Contracts](../Contracts.lean), as for invocation.
The conclusions keep rollback before publication and committed initialization/start effects after
it visible in the source outcome.
-/

open Aeneas Aeneas.Std SpecExt

namespace Exec

open Itasca Theorems Store

/-- Actual accepted compilation and public instantiation choose the final code interpretation after
all start callbacks. The full invariant, agreement on old issued keys, raw prefix and cross-world
source extension use that same choice. No interpretation of freshly published keys is fixed in
advance. `EventfulInstantiationSourceOutcome` separates failure before publication, which rolls
back, from failure after publication, which retains initialization and start effects. The module is
also source-typed. This is partial correctness: a start function may diverge. -/
theorem runtime.store.instantiate.Store.instantiate_with.sound {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (correct : Platform.FloatOpsCorrect floats)
    (law : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (oldCode : CodeInterpretation) (old : ExecutableInv view oldCode before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (bytes : Slice U8) (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module))
    (raw : ModuleBinary.Module)
    (encoded : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile)
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀ c store, ExecutableInv view c store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer → Interp.FrameStorePrefix store answer.2.2.1)
    (externs : ∀ c store, ExecutableInv view c store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length)
    (issued : ∀ c store, ExecutableInv view c store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer →
      ∀ value ∈ answer.2.2.2.val, IssuedValue answer.2.2.1 value) :
    Module_ok (ModuleElaboration.moduleOf raw) ∧
      runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
        ⦃ out => ∃ afterCode, CodeAgreesOn before oldCode afterCode ∧
          ExecutableInv view afterCode out.2.1 ∧ Interp.FrameStorePrefix before out.2.1 ∧
          Extend_store (decodeStore view oldCode before)
            (decodeStore view afterCode out.2.1) ∧
          EventfulInstantiationSourceOutcome view oldCode
            afterCode before module imports raw platform
            out.1 out.2.1 out.2.2 ⦄div :=
  instantiate_compiled_executable_world_source memory hooks floats allocator view laws correct law
    interrupts before module imports platform oldCode old handles bytes profile limits accepted raw
    encoded sound preserve externs issued

/-- `sound` with the exact event log returned by the transparent instantiation recorder
`recordedInstantiateWith`, and with a classified resource cause for every error. One final code
interpretation serves all guarantees. -/
theorem runtime.store.instantiate.Store.instantiate_with.recorded_sound {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (correct : Platform.FloatOpsCorrect floats)
    (law : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (oldCode : CodeInterpretation) (old : ExecutableInv view oldCode before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (bytes : Slice U8) (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module))
    (raw : ModuleBinary.Module)
    (encoded : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile)
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀ c store, ExecutableInv view c store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer → Interp.FrameStorePrefix store answer.2.2.1)
    (externs : ∀ c store, ExecutableInv view c store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length)
    (issued : ∀ c store, ExecutableInv view c store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer →
      ∀ value ∈ answer.2.2.2.val, IssuedValue answer.2.2.1 value) :
    Module_ok (ModuleElaboration.moduleOf raw) ∧
      runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
        ⦃ out => ∃ events, recordedInstantiateWith memory hooks floats allocator before module imports platform [] = .ok (out,events) ∧
          ∃ afterCode, CodeAgreesOn before oldCode afterCode ∧
          ExecutableInv view afterCode out.2.1 ∧ Interp.FrameStorePrefix before out.2.1 ∧
          Extend_store (decodeStore view oldCode before)
            (decodeStore view afterCode out.2.1) ∧
          RecordedInstantiationSourceOutcome view oldCode
            afterCode before module imports raw platform
            events out.1 out.2.1 out.2.2 ∧
          (∀error,out.1=.Err error → WorldExecutableInstantiationResourceCause memory hooks floats allocator
            view oldCode before module imports platform raw out.2.1 error) ⦄div :=
  instantiate_compiled_executable_world_recording_resources memory hooks floats allocator view laws
    correct law interrupts before module imports platform oldCode old handles bytes profile limits
    accepted raw encoded sound preserve externs issued

end Exec
