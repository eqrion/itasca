import Exec.Store.Initialization.SegmentInitialize
import Exec.Code.Module.CompileSemantic

namespace Exec.Store
open Aeneas Aeneas.Std

/-- A successfully compiled module supplies both the retained program and all
source typing/PC bounds for actual segment initialization. The remaining
premises are the issued instance maps produced by linking and staging. -/
theorem initialize_segments_compiled {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex : Usize)
    (inst : runtime.store.ModuleInst) (bytes : Slice U8) (profile : Itasca.ValidationProfile)
    (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module))
    (found : store.instances.val[instIndex.val]? = some inst)
    (shape : InstanceShape store inst) (imports : InitializerImports store inst)
    (bindings : InitializerBindings store inst) :
    runtime.interp.initialize_segments memory hooks floats allocator store platform instIndex
      ⦃ out => SegmentAddressSpace store out.2.1 ∧ out.2.2 = platform ⦄ := by
  obtain ⟨witness⟩ := Code.compile_accepted allocator bytes profile limits inst.module accepted
  obtain ⟨code, functionFound, program⟩ := witness.segment_program law
  obtain ⟨valid, dataValid⟩ := witness.semantic law
  have pcBound := Code.segment_compile_pc_bound allocator law bytes profile limits inst.module accepted code program
  exact initialize_segments_program_total memory hooks floats allocator view laws law store platform instIndex inst code
    found functionFound program pcBound shape imports bindings valid.elements dataValid

end Exec.Store
