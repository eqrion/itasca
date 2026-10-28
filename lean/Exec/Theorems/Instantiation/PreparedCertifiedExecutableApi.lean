import Exec.Theorems.Api.CertifiedApi
import Exec.Theorems.Instantiation.PreparedCertifiedExecutable
import Exec.Store.Instantiation.PreparedExportBounds
import Exec.Store.Instantiation.PreparedRunShape
import Exec.Store.Instantiation.PreparedRunGlobalTypes
import Exec.Store.Instantiation.PreparedRunTableMemory
import Exec.Store.Instantiation.PreparedRunBounds
import Exec.Theorems.Composition.Executable.ExecutableInstantiationSource
import Exec.Store.Invariant.ExecutableInstantiationCode
import Exec.Code.Module.CompileDataCount
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std Itasca Store

/-- The actual preparation trace constructs source typing and retained compiler
certificates for the fresh store, including all old functions and instances. -/
theorem prepared_certified_executable_api {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform : P} {ready : runtime.store.Store M}
    (trace : PreparedRun memory hooks floats allocator view before module platform ready)
    (laws : Platform.MemoryLaws memory view) (law : Platform.AllocCorrect allocator)
    (oldCode : CodeInterpretation) (old : CertifiedExecutableApiStore view oldCode before)
    (accounted : SegmentAccounting before)
    {tables memories} (cache : ModuleEnv.Cache module.module.env tables memories)
    (valid : ModuleEnv.Valid module.module.env module.profile)
    (initializers : Code.InitializerMappings module)
    (raw : ModuleBinary.Module)
    (elaborated : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (typed : Module_ok (ModuleElaboration.moduleOf raw))
    (matched : ModuleElaboration.Matches module.module.env module.module.tail raw)
    {profile bytes}
    (encoded : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes profile)
    (functions : Code.ExecutableModuleFunctions module (Code.sourceFunctions raw))
    (dataCount : ∀ count, module.module.env.data_count = some count →
      count.val = module.module.tail.data.val.length)
    (bounds : SegmentBounds ready) :
    ∃ inst, ready.instances.val[before.instances.len.val]? = some inst ∧ inst.module = module ∧
      CertifiedExecutableApiStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) ready ∧
      SegmentAccounting ready ∧
      Abs.ModuleBindings (decodeStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) ready)
        (decodeInstance ready inst) (ModuleElaboration.contextOf raw) := by
  obtain ⟨inst,found,source,certified,counted,bindings⟩ :=
    prepared_certified_executable trace laws law oldCode old.toCertifiedSupportedStore accounted
      cache valid initializers raw elaborated typed matched encoded functions dataCount bounds
  exact ⟨inst,found,source,⟨certified,trace.export_bounds laws law old.shape accounted cache valid initializers old.exportBounds⟩,
    counted,bindings⟩
end Itasca.Runtime.Theorems
