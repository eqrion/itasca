import Exec.Store.Initialization.SegmentReady

namespace Exec.Store
open Aeneas Aeneas.Std
open Exec.Interp

/-- Syntactic and issued-address requirements of one initializer instruction.
There are no interpreter executions or semantic postconditions in this record. -/
inductive SegmentInstructionReady {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.Instance) (code : runtime.bytecode.CompiledFunction) (width : Nat) :
    runtime.bytecode.Instr → Prop where
  | constant (dst bits : U32) (bound : dst.val < width) :
      SegmentInstructionReady store inst code width (.Const32 dst bits)
  | global (index : U32) (addr : runtime.GlobalAddr) (value : runtime.store.GlobalInstance)
      (mapped : inst.globals.val[index.val]? = some addr)
      (issued : store.globals.val[addr.index.val]? = some value) (capacity : 1 ≤ width) :
      SegmentInstructionReady store inst code width (.GlobalGet 0#u32 index)
  | bulk (instruction : runtime.bytecode.Instr) (ready : SegmentBulkReady store inst code instruction)
      (capacity : (∃ entry, instruction = .MemoryInit 0#u32 entry ∨ instruction = .TableInit 0#u32 entry) → 3 ≤ width) :
      SegmentInstructionReady store inst code width instruction
  | done : SegmentInstructionReady store inst code width (.Return 0#u32 0#u32)

theorem SegmentInstructionReady.transport {M : Type} {store after : runtime.store.Store M}
    {inst code width instruction} (ready : SegmentInstructionReady store inst code width instruction)
    (same : SegmentAddressSpace store after) : SegmentInstructionReady after inst code width instruction := by
  cases ready with
  | constant dst bits bound => exact .constant dst bits bound
  | global index addr value mapped issued capacity =>
    exact .global index addr value mapped (by rw [same.globals]; exact issued) capacity
  | bulk instruction ready capacity => exact .bulk instruction (ready.transport same) capacity
  | done => exact .done

def segmentReturns : runtime.bytecode.Instr → Bool
  | .Return _ _ => true
  | _ => false

structure SegmentStepEffect {M P : Type} (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (platform : P) (instIndex function : Usize) (position : U32) (instruction : runtime.bytecode.Instr)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : Prop where
  status : SegmentStatus out.1
  slots : out.2.1.slots.length = exec.slots.length
  metadata : SegmentAddressSpace store out.2.2.1
  platform : out.2.2.2 = platform
  frames : if segmentReturns instruction then out.2.1.frames.val = [] else
    ∃ next : U32, next.val = position.val + 1 ∧ out.2.1.frames.val = [initializerFrame instIndex function next]

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem segment_instruction_total (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (instIndex function : Usize) (position : U32) (inst : runtime.store.Instance)
    (code : runtime.bytecode.CompiledFunction) (instruction : runtime.bytecode.Instr)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (frames : exec.frames.val = [initializerFrame instIndex function position])
    (fetched : code.code.val[position.val]? = some instruction)
    (pcBound : position.val < U32.max)
    (ready : SegmentInstructionReady store inst code exec.slots.length instruction) :
    runtime.interp.step memory hooks floats allocator exec store platform
      ⦃ out => SegmentStepEffect exec store platform instIndex function position instruction out ⦄ := by
  cases ready with
  | constant dst bits bound =>
    apply WP.spec_mono (segment_step_const32 memory hooks floats allocator exec store platform instIndex function position
      inst code dst bits found functionFound frames fetched pcBound bound)
    rintro out ⟨success, next, nextValue, effect, rfl, rfl⟩
    refine ⟨Or.inl success, by simp only [alloc.vec.Vec.length, effect.1, List.length_set], .refl _, rfl, ?_⟩
    simp only [segmentReturns, Bool.false_eq_true, ↓reduceIte]
    refine ⟨next, nextValue, ?_⟩
    have same := congrArg (fun e : runtime.interp.Execution => e.frames.val) effect.2
    simpa [frames] using same
  | global index addr value mapped issued capacity =>
    apply WP.spec_mono (segment_step_read memory hooks floats allocator exec store platform instIndex function position
      inst code _ [value.lo] found functionFound (.global index addr value mapped issued)
      (by simpa using capacity) frames fetched pcBound)
    rintro out ⟨success, slots, next, nextValue, frames, rfl, rfl⟩
    refine ⟨Or.inl success, ?_, .refl _, rfl, ?_⟩
    · rw [alloc.vec.Vec.length, slots, initialSlots_length]
    · exact ⟨next, nextValue, frames⟩
  | bulk instruction ready capacity =>
    apply WP.spec_mono (segment_step_bulk memory hooks floats allocator exec store platform instIndex function position
      inst code instruction ready.kind found functionFound frames fetched pcBound _
      (segment_bulk_total memory view laws store instIndex function (alloc.vec.Vec.deref exec.slots)
        inst code instruction found functionFound (by simpa [alloc.vec.Vec.deref, alloc.vec.Vec.length] using capacity) ready))
    rintro out ⟨next, nextValue, effect, rfl, status, metadata⟩
    refine ⟨status, by rw [effect], metadata, rfl, ?_⟩
    have nonReturn : segmentReturns instruction = false := by cases ready <;> rfl
    simp only [nonReturn, Bool.false_eq_true, ↓reduceIte]
    rw [effect]
    exact ⟨next, nextValue, by simp [frames]⟩
  | done =>
    apply WP.spec_mono (segment_step_return memory hooks floats allocator exec store platform instIndex function position
      inst code 0#u32 found functionFound (by simp) frames fetched pcBound)
    rintro out ⟨success, slots, empty, rfl, rfl⟩
    exact ⟨Or.inl success, by rw [slots], .refl _, rfl, by simpa [segmentReturns] using empty⟩

end Exec.Store
