import Exec.Store.Instantiation.InstantiateDecomposition
import Exec.Store.Instantiation.InstantiateStart
import Exec.Store.Instantiation.InstantiateCompiledNoStart
import Exec.Code.Module.CompileCache

namespace Exec.Store
open Aeneas Aeneas.Std

/-- Complete actual preparation and segment execution either reject before
commit, return normally after commit, or reach the exact source-typed start
call. The compiler module certificate constructs all new code coverage; no
premise states execution correctness of the installed functions. -/
theorem instantiate_compiled_code_ready {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (bytes : Slice U8) (profile : Itasca.ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module))
    (shape : Shape view before) (accounted : SegmentAccounting before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (oldCode : CodeInterpretation) (oldCompiled : Interp.CompiledFunctions oldCode before)
    (sources : List funccode) (certificate : Code.ModuleFunctions module sources) :
    (∃ error staged,
      runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false =
        .ok (.Err error, staged, platform, false) ∧ StagedPrefix before staged) ∨
    (∃ initialized, Shape view initialized ∧ SegmentAccounting initialized ∧
      Interp.CompiledFunctions (installCode oldCode before.instances.len.val sources) initialized ∧
      ((∃ result,
        runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false =
          .ok (result, initialized, platform, true)) ∨
       ∃ address function signature,
         address.store = initialized.id ∧ initialized.funcs.val[address.index.val]? = some function ∧
         initialized.types.val[function.signature.val]? = some signature ∧
         signature.params.val = [] ∧ signature.results.val = [] ∧
         runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false =
           instantiate_start memory hooks floats allocator ⟨before.id, before.instances.len⟩ address initialized platform)) := by
  obtain ⟨witness⟩ := Code.compile_accepted allocator bytes profile limits module accepted
  obtain ⟨tables, memories, cache⟩ := witness.cache law
  have certificates := witness.initializers law
  obtain ⟨valid, dataValid⟩ := witness.semantic law
  have moduleValid : Itasca.ModuleEnv.Valid module.module.env module.profile := by
    rw [certificates.2.1]
    exact valid
  have parts := instantiate_inner_decomposition memory hooks floats allocator law view laws before module
    imports platform shape accounted cache moduleValid dataValid certificates.2.2.2 handles _ rfl
  rcases parts with rejected | ⟨ready, inst, readyShape, found, source, initialized, types, readyAccounting, code, continued⟩
  · exact Or.inl rejected
  · have acceptedInst : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module) := by
      rw [source]
      exact accepted
    have compiled := code.compiled oldCode shape oldCompiled found sources
      (by simpa only [source] using certificate) (by simpa only [source] using cache)
    obtain ⟨after, afterShape, metadata, completed⟩ := instantiate_tail_start_ready memory hooks floats allocator
      view laws law ready platform ⟨before.id, before.instances.len⟩ inst bytes profile limits acceptedInst
      found readyShape initialized types code.function_table
    refine Or.inr ⟨after, afterShape, metadata.accounting readyAccounting,
      metadata.compiled _ compiled, ?_⟩
    rcases completed with ⟨result, returned⟩ | ⟨address, function, signature, owned, resolved, typed, params, results, call⟩
    · exact Or.inl ⟨result, continued.symm.trans returned⟩
    · exact Or.inr ⟨address, function, signature, owned, resolved, typed, params, results, continued.symm.trans call⟩

end Exec.Store
