import Exec.Store.Initialization.SegmentBulkMetadata
import Exec.Store.Initialization.SegmentInstruction

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.Runtime.Interp

theorem segment_instruction_object_metadata {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (instIndex function : Usize) (position : U32) (inst : runtime.store.ModuleInst)
    (code : runtime.bytecode.CompiledFunction) (instruction : runtime.bytecode.Instr)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (frames : exec.frames.val = [initializerFrame instIndex function position])
    (fetched : code.code.val[position.val]? = some instruction)
    (pcBound : position.val < U32.max)
    (ready : SegmentInstructionReady store inst code exec.slots.length instruction) :
    runtime.interp.step memory hooks floats allocator exec store platform
      ⦃ out => SegmentObjectMetadata view store out.2.2.1 ⦄ := by
  cases ready with
  | constant dst bits bound =>
    apply WP.spec_mono (segment_step_const32 memory hooks floats allocator exec store platform instIndex function position
      inst code dst bits found functionFound frames fetched pcBound bound)
    rintro out ⟨success, next, nextValue, effect, rfl, rfl⟩
    exact .refl _ _
  | global index addr value mapped issued capacity =>
    apply WP.spec_mono (segment_step_read memory hooks floats allocator exec store platform instIndex function position
      inst code _ [value.lo] found functionFound (.global index addr value mapped issued)
      (by simpa using capacity) frames fetched pcBound)
    rintro out ⟨success, slots, next, nextValue, frames, rfl, rfl⟩
    exact .refl _ _
  | bulk instruction ready capacity =>
    apply WP.spec_mono (segment_step_bulk memory hooks floats allocator exec store platform instIndex function position
      inst code instruction ready.kind found functionFound frames fetched pcBound _
      (segment_bulk_object_metadata memory view laws store instIndex function (alloc.vec.Vec.deref exec.slots)
        inst code instruction found functionFound (by simpa [alloc.vec.Vec.deref, alloc.vec.Vec.length] using capacity)
        ready))
    rintro out ⟨next, nextValue, effect, rfl, metadata⟩
    exact metadata
  | done =>
    apply WP.spec_mono (segment_step_return memory hooks floats allocator exec store platform instIndex function position
      inst code 0#u32 found functionFound (by simp) frames fetched pcBound)
    rintro out ⟨success, slots, empty, rfl, rfl⟩
    exact .refl _ _

end Itasca.Runtime.Store
