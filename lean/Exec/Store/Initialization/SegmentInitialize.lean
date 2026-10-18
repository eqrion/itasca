import Exec.Store.Initialization.SegmentSynthetic
import Exec.Code.Module.SegmentSource

namespace Exec.Store
open Aeneas Aeneas.Std

/-- The actual instantiation segment entry point returns normally for the
compiler's retained program and issued instance maps. -/
theorem initialize_segments_total {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex : Usize)
    (inst : runtime.store.Instance) (code : runtime.bytecode.CompiledFunction)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[inst.module.initialization.val]? = some code)
    (ready : SegmentCodeReady store inst code code.slot_count.val) :
    runtime.instantiate.initialize_segments memory hooks floats allocator store platform instIndex
      ⦃ out => SegmentAddressSpace store out.2.1 ∧ out.2.2 = platform ⦄ := by
  unfold runtime.instantiate.initialize_segments
  step with Interp.vec_index_given store.instances instIndex inst found as ⟨actual, equal⟩
  subst actual
  step with segment_synthetic_total memory hooks floats allocator view laws law store platform instIndex
    inst.module.initialization inst code found functionFound ready as ⟨result, after, host, metadata, hostEq⟩
  subst host
  cases result <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Source typing and the syntactic emitted-program certificate discharge all
machine-readiness obligations; no execution-safety premise is required. -/
theorem initialize_segments_program_total {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex : Usize)
    (inst : runtime.store.Instance) (code : runtime.bytecode.CompiledFunction)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[inst.module.initialization.val]? = some code)
    (program : Code.SegmentProgram inst.module code) (pcBound : code.code.length < U32.max)
    (shape : InstanceShape store inst) (imports : InitializerImports store inst)
    (bindings : InitializerBindings store inst)
    (elementsValid : ∀ segment ∈ inst.module.module.env.elements.val,
      Itasca.ModuleSegments.elementValid inst.module.module.env segment)
    (dataValid : ∀ segment ∈ inst.module.module.tail.data.val,
      Itasca.ModuleData.Valid inst.module.module.env segment) :
    runtime.instantiate.initialize_segments memory hooks floats allocator store platform instIndex
      ⦃ out => SegmentAddressSpace store out.2.1 ∧ out.2.2 = platform ⦄ :=
  initialize_segments_total memory hooks floats allocator view laws law store platform instIndex inst code
    found functionFound (segment_program_ready store inst code program pcBound shape imports bindings elementsValid dataValid)

end Exec.Store
