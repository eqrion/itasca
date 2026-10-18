import Exec.Store.Initialization.BulkPreservation
import Exec.Interp.Relations.Initializer

/-! Straight-line initialization steps reuse the actual interpreter fetch and
dispatch path, with exact program-counter and metadata effects. -/
namespace Exec.Store
open Aeneas Aeneas.Std
open Exec.Interp

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem segment_step_read (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize) (position : U32)
    (inst : runtime.store.Instance) (code : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (read : InitialRead store inst code instruction words)
    (capacity : words.length ≤ exec.slots.length)
    (hf : exec.frames.val = [initializerFrame instIndex function position])
    (hop : code.code.val[position.val]? = some instruction)
    (pcBound : position.val < U32.max) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.slots.val = initialSlots exec.slots.val words ∧
      ∃ next : U32, next.val = position.val + 1 ∧ out.2.1.frames.val = [initializerFrame instIndex function next] ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform 0#usize
    (initializerFrame instIndex function position) inst code instruction
    (by simpa [alloc.vec.Vec.length, hf]) (by simp [hf]) hi hc hop (by simpa [initializerFrame] using pcBound)
  intro next hnext
  apply WP.spec_mono (dispatch_initial_read memory hooks floats allocator
    { exec with frames := exec.frames.set 0#usize (initializerFrame instIndex function next) }
    store platform instIndex function 0#usize inst code instruction words hi hc read capacity)
  rintro out ⟨hok, ⟨hslots, hrest⟩, hs, hp⟩
  have hframes := congrArg runtime.interp.Execution.frames hrest
  exact ⟨hok, hslots, next, hnext, by simpa [hf] using congrArg alloc.vec.Vec.val hframes, hs, hp⟩


/-- Administrative bulk dispatch preserves the entire execution record and
passes through precisely the ordinary success/trap result of the checked bulk
handler. This is a composition rule, not a machine-correctness premise. -/
theorem segment_admin_bulk (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (inst function base : Usize)
    (instruction : runtime.bytecode.Instr)
    (post : core.result.Result Unit runtime.ExecError × runtime.store.Store M → Prop)
    (bulk : runtime.interp.bulk.execute memory store inst function base
      (alloc.vec.Vec.deref exec.slots) instruction ⦃ post ⦄) :
    runtime.interp.admin_memory_fill memory hooks floats allocator exec store inst function base instruction
      ⦃ out => out.2.1 = exec ∧ post (out.1, out.2.2) ⦄ := by
  unfold runtime.interp.admin_memory_fill
  step with bulk as ⟨result, after, effect⟩
  cases result <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame]

inductive SegmentBulk : runtime.bytecode.Instr → Prop where
  | memory (data : U32) : SegmentBulk (.MemoryInit 0#u32 data)
  | table (entry : U32) : SegmentBulk (.TableInit 0#u32 entry)
  | dataDrop (data : U32) : SegmentBulk (.DataDrop data)
  | elementDrop (element : U32) : SegmentBulk (.ElemDrop element)

theorem segment_dispatch_bulk (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (frameIndex inst function : Usize)
    (instruction : runtime.bytecode.Instr) (kind : SegmentBulk instruction)
    (post : core.result.Result Unit runtime.ExecError × runtime.store.Store M → Prop)
    (bulk : runtime.interp.bulk.execute memory store inst function 0#usize
      (alloc.vec.Vec.deref exec.slots) instruction ⦃ post ⦄) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex
      inst function 0#usize instruction
      ⦃ out => out.2.1 = exec ∧ out.2.2.2 = platform ∧ post (out.1, out.2.2.1) ⦄ := by
  cases kind <;> simp only [runtime.interp.dispatch] <;>
    step with segment_admin_bulk memory hooks floats allocator exec store inst function 0#usize _ post bulk <;>
    simp_all

theorem segment_step_return (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize) (position : U32)
    (inst : runtime.store.Instance) (code : runtime.bytecode.CompiledFunction) (width : U32)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (capacity : width.val ≤ exec.slots.length)
    (hf : exec.frames.val = [initializerFrame instIndex function position])
    (hop : code.code.val[position.val]? = some (.Return 0#u32 width))
    (pcBound : position.val < U32.max) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.slots = exec.slots ∧ out.2.1.frames.val = [] ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform 0#usize
    (initializerFrame instIndex function position) inst code (.Return 0#u32 width)
    (by simpa [alloc.vec.Vec.length, hf]) (by simp [hf]) hi hc hop (by simpa [initializerFrame] using pcBound)
  intro pc hpc
  simp only [runtime.interp.dispatch, initializerFrame]
  step with initializer_return_effect memory hooks floats allocator
    { exec with frames := exec.frames.set 0#usize { «instance» := instIndex, function := function, pc := pc, base := 0#usize } }
    width capacity
  simp_all [hf]


theorem segment_step_bulk (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize) (position : U32)
    (inst : runtime.store.Instance) (code : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (kind : SegmentBulk instruction)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (hf : exec.frames.val = [initializerFrame instIndex function position])
    (hop : code.code.val[position.val]? = some instruction)
    (pcBound : position.val < U32.max)
    (post : core.result.Result Unit runtime.ExecError × runtime.store.Store M → Prop)
    (bulk : runtime.interp.bulk.execute memory store instIndex function 0#usize
      (alloc.vec.Vec.deref exec.slots) instruction ⦃ post ⦄) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      ∃ next : U32, next.val = position.val + 1 ∧
        out.2.1 = {exec with frames := exec.frames.set 0#usize (initializerFrame instIndex function next)} ∧
        out.2.2.2 = platform ∧ post (out.1, out.2.2.1) ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform 0#usize
    (initializerFrame instIndex function position) inst code instruction
    (by simpa [alloc.vec.Vec.length, hf]) (by simp [hf]) hi hc hop
    (by simpa [initializerFrame] using pcBound)
  intro next hnext
  apply WP.spec_mono (segment_dispatch_bulk memory hooks floats allocator
    {exec with frames := exec.frames.set 0#usize (initializerFrame instIndex function next)}
    store platform 0#usize instIndex function instruction kind post bulk)
  intro out effect
  exact ⟨next, hnext, effect⟩

theorem segment_step_const32 (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize) (position : U32)
    (inst : runtime.store.Instance) (code : runtime.bytecode.CompiledFunction) (dst bits : U32)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (hf : exec.frames.val = [initializerFrame instIndex function position])
    (hop : code.code.val[position.val]? = some (.Const32 dst bits))
    (pcBound : position.val < U32.max) (capacity : dst.val < exec.slots.length) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ ∃ next : U32, next.val = position.val + 1 ∧
        SlotsEffect {exec with frames := exec.frames.set 0#usize (initializerFrame instIndex function next)}
          out.2.1 (exec.slots.val.set dst.val (UScalar.cast .U64 bits)) ∧
        out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform 0#usize
    (initializerFrame instIndex function position) inst code (.Const32 dst bits)
    (by simpa [alloc.vec.Vec.length, hf]) (by simp [hf]) hi hc hop
    (by simpa [initializerFrame] using pcBound)
  intro next hnext
  simp only [runtime.interp.dispatch, initializerFrame]
  have effect := const32_effect memory hooks floats allocator
    {exec with frames := exec.frames.set 0#usize (initializerFrame instIndex function next)}
    0#usize dst bits (by simpa using capacity)
  simp only [initializerFrame] at effect
  step with effect as ⟨status, after, success, slots⟩
  simp only [Nat.zero_add] at slots
  simpa only [success, true_and, and_true, initializerFrame] using (show ∃ next : U32, next.val = position.val + 1 ∧ SlotsEffect {exec with frames := exec.frames.set 0#usize (initializerFrame instIndex function next)} after (exec.slots.val.set dst.val (UScalar.cast .U64 bits)) from ⟨next, hnext, slots⟩)

end Exec.Store
