import Exec.Store.Initialization.SegmentSyntheticBounds
import Exec.Store.Initialization.SegmentCompatibility
import Exec.Store.Initialization.SegmentAccepted

namespace Exec.Store
open Aeneas Aeneas.Std

theorem initialize_segments_bounds {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex : Usize)
    (inst : runtime.store.Instance) (code : runtime.bytecode.CompiledFunction)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[inst.module.initialization.val]? = some code)
    (ready : SegmentCodeReady store inst code code.slot_count.val)
    (bounded : SegmentBounds store) :
    runtime.instantiate.initialize_segments memory hooks floats allocator store platform instIndex
      ⦃ out => SegmentBounds out.2.1 ⦄ := by
  unfold runtime.instantiate.initialize_segments
  step with Interp.vec_index_given store.instances instIndex inst found as ⟨actual, equal⟩
  subst actual
  step with segment_synthetic_bounds memory hooks floats allocator view laws law store platform instIndex
    inst.module.initialization inst code found functionFound ready bounded as ⟨result, after, host, afterBounds⟩
  cases result <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]


/-- Canonically compiled initialization preserves the full structural Store
invariant, assuming the source/raw reference-type maps established by staging. -/
theorem initialize_segments_compiled_bounds {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex : Usize)
    (inst : runtime.store.Instance) (bytes : Slice U8) (profile : Itasca.ValidationProfile)
    (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module))
    (found : store.instances.val[instIndex.val]? = some inst)
    (shape : Shape view store) (imports : InitializerImports store inst)
    (bindings : InitializerBindings store inst) (bounded : SegmentBounds store) :
    runtime.instantiate.initialize_segments memory hooks floats allocator store platform instIndex
      ⦃ out => SegmentBounds out.2.1 ⦄ := by
  obtain ⟨witness⟩ := Code.compile_accepted allocator bytes profile limits inst.module accepted
  obtain ⟨code, functionFound, program⟩ := witness.segment_program law
  obtain ⟨valid, dataValid⟩ := witness.semantic law
  have pcBound := Code.segment_compile_pc_bound allocator law bytes profile limits inst.module accepted code program
  have instanceShape := shape.instances inst (List.mem_of_getElem? found)
  have ready := segment_program_ready store inst code program pcBound instanceShape imports bindings valid.elements dataValid
  exact initialize_segments_bounds memory hooks floats allocator view laws law store platform instIndex inst code
    found functionFound ready bounded

end Exec.Store
