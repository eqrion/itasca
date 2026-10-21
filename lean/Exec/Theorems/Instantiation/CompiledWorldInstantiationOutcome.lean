import Exec.Theorems.Instantiation.InstantiateExecutableEventfulSource
import Exec.Theorems.Host.HostWorldSound

/-! Ordinary compiled-instantiation package, independent of its public construction. -/
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store SpecExt
/-- Successful compilation chooses the canonical source syntax before the
callback contract carries the current code interpretation through publication. -/
def CompiledWorldInstantiation {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (before : runtime.store.Store M)
    (module : runtime.compiler.ExecutableModule) (imports : Slice runtime.Extern)
    (platform : P) (oldCode : CodeInterpretation) (bytes : Slice U8)
    (profile : ValidationProfile) : Prop :=
  ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧
    Module_ok (ModuleElaboration.moduleOf raw) ∧
    ∀ (_sound : HostWorldSound hooks view (ExecutableInv view))
    (_preserve : ∀ c store, ExecutableInv view c store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer → Interp.FrameStorePrefix store answer.2.2.1)
    (_externs : ∀ c store, ExecutableInv view c store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length)
    (_issued : ∀ c store, ExecutableInv view c store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer →
      ∀ value ∈ answer.2.2.2.val, IssuedValue answer.2.2.1 value),
      runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
        ⦃ out => ∃ afterCode, CodeAgreesOn before oldCode afterCode ∧
          ExecutableInv view afterCode out.2.1 ∧ Interp.FrameStorePrefix before out.2.1 ∧
          Extend_store (decodeStore view oldCode before) (decodeStore view afterCode out.2.1) ∧
          EventfulInstantiationSourceOutcome view oldCode afterCode before module imports raw platform
            out.1 out.2.1 out.2.2 ⦄div

end Exec.Theorems
