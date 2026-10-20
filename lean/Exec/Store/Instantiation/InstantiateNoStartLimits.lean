import Exec.Store.Instantiation.InstantiateNoStartStructure

namespace Exec.Store
open Aeneas Aeneas.Std

/-- Actual public instantiation of an accepted module without a start function
returns normally and preserves the complete structural store invariant. Linking,
allocation refusal, and segment bounds traps are ordinary returned errors;
uncommitted errors roll back exactly. No premise assumes instantiation safety. -/
theorem instantiate_compiled_no_start_limits {M P F A : Type}
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
    (noStart : module.module.env.start = none) :
    runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
      ⦃ out => Shape view out.2.1 ∧ SegmentAccounting out.2.1 ∧ out.2.2 = platform ∧
        out.2.1.limits = before.limits ∧
        (∀ address, out.1 = .Ok address → address.store = out.2.1.id ∧
          ∃ inst, out.2.1.instances.val[address.index.val]? = some inst ∧ inst.module = module) ⦄ := by
  apply WP.spec_mono (instantiate_compiled_no_start_structure memory hooks floats allocator view laws law
    before module imports platform bytes profile limits accepted shape accounted handles noStart)
  rintro out ⟨shape, accounting, host, externs, limits, issued⟩
  exact ⟨shape, accounting, host, limits, issued⟩

end Exec.Store
