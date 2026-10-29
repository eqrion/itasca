import Itasca.Runtime.Interp.Relations.Conditional
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- The extracted jump table performs exactly one unsigned selection and
changes only the current frame's PC. The last table entry is the default. -/
theorem jump_table_effect {M : Type}
    (memory : runtime.platform.MemoryBuffer M)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (frameIndex instanceIndex functionIndex base : Usize) (index start len : U32)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (slot : U64) (target : U32)
    (frameBound : frameIndex.val < exec.frames.length)
    (slotLookup : exec.slots.val[base.val + index.val]? = some slot)
    (instanceLookup : store.instances.val[instanceIndex.val]? = some inst)
    (functionLookup : inst.module.functions.val[functionIndex.val]? = some compiled)
    (nonempty : 0 < len.val)
    (tableBound : start.val + (len.val - 1) ≤ U32.max)
    (targetLookup : compiled.jump_tables.val[start.val + Nat.min (UScalar.cast .U32 slot).val (len.val - 1)]? = some target) :
    runtime.interp.execute_jump_table memory exec store frameIndex
      instanceIndex functionIndex base index start len ⦃ out =>
      out.1 = .Ok () ∧ JumpEffect exec out.2.1 frameIndex.val target ∧ out.2.2 = store ⦄ := by
  have indexCast : (UScalar.cast .Usize index).val = index.val := by scalar_tac
  have slotBound := (List.getElem?_eq_some_iff.mp slotLookup).1
  unfold runtime.interp.execute_jump_table
  step as ⟨position,positionEq⟩
  step as ⟨slotIndex,slotIndexEq⟩
  step with vec_index_given exec.slots slotIndex slot (by simpa only [slotIndexEq,positionEq,indexCast] using slotLookup) as ⟨actual,actualEq⟩
  subst actual
  step as ⟨selector,selectorEq⟩
  step as ⟨last,lastEq⟩
  split
  all_goals
    step with vec_index_given store.instances instanceIndex inst instanceLookup as ⟨actual,actualEq⟩
    subst actual
    step with vec_index_given inst.module.functions functionIndex compiled functionLookup as ⟨actual,actualEq⟩
    subst actual
    step as ⟨tableIndex,tableIndexEq⟩
    step as ⟨tablePosition,tablePositionEq⟩
    have selectedEq : tablePosition.val = start.val + Nat.min (UScalar.cast .U32 slot).val (len.val-1) := by
      rw [tablePositionEq]
      have castTable : (UScalar.cast .Usize tableIndex).val = tableIndex.val := by scalar_tac
      rw [castTable,tableIndexEq]
      simp only [Nat.min_def]
      split <;> scalar_tac
    step with vec_index_given compiled.jump_tables tablePosition target (by simpa only [selectedEq] using targetLookup) as ⟨actual,actualEq⟩
    subst actual
    step* <;> simp_all [JumpEffect,getElem!_pos]
theorem dispatch_jump_table_exact {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (index start len target : U32) (value : Nat)
    (frameLookup : exec.frames.val[frameIndex.val]? = some raw)
    (instanceLookup : store.instances.val[raw.instance.val]? = some inst)
    (functionLookup : inst.module.functions.val[raw.function.val]? = some compiled)
    (bound : value < 2^32)
    (input : WordsAt exec.slots.val (raw.base.val + index.val) [value])
    (nonempty : 0 < len.val) (tableBound : start.val + (len.val-1) ≤ U32.max)
    (targetLookup : compiled.jump_tables.val[start.val + Nat.min value (len.val-1)]? = some target) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex
      raw.instance raw.function raw.base (.JumpTable index start len) ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = {exec with frames := exec.frames.set frameIndex {raw with pc := target}} ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  have frameBound := (List.getElem?_eq_some_iff.mp frameLookup).1
  have slotBound : raw.base.val + index.val < exec.slots.length := by simpa using (input 0 (by simp)).1
  have bits : exec.slots.val[raw.base.val + index.val]!.val = value := by simpa using (input 0 (by simp)).2
  have cast : (UScalar.cast .U32 exec.slots.val[raw.base.val+index.val]!).val = value := by
    simp only [UScalar.cast_val_eq,UScalarTy.numBits,bits,Nat.mod_eq_of_lt bound]
  have slotLookup : exec.slots.val[raw.base.val+index.val]? = some exec.slots.val[raw.base.val+index.val]! := by
    simp only [List.getElem?_eq_getElem slotBound,_root_.getElem!_pos exec.slots.val (raw.base.val + index.val) slotBound]
  obtain ⟨out,run,success,effect,sameStore⟩ := WP.spec_imp_exists
    (jump_table_effect memory exec store frameIndex raw.instance raw.function raw.base
      index start len inst compiled _ target frameBound slotLookup instanceLookup functionLookup nonempty tableBound
      (by simpa only [cast] using targetLookup))
  have exactState := effect.exact frameLookup
  simp only [runtime.interp.dispatch,run,bind_ok]
  apply WP.spec.ret
  exact ⟨success,exactState,sameStore,rfl⟩

theorem step_jump_table_exact {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (selector start len target : U32) (value : Nat)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (fetched : compiled.code.val[raw.pc.val]? = some (.JumpTable selector start len))
    (bound : value < 2^32)
    (input : WordsAt exec.slots.val (raw.base.val + selector.val) [value])
    (nonempty : 0 < len.val) (tableBound : start.val + (len.val-1) ≤ U32.max)
    (targetLookup : compiled.jump_tables.val[start.val + Nat.min value (len.val-1)]? = some target) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧
      out.2.1 = { exec with frames := exec.frames.set index { raw with pc := target } } ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
    (.JumpTable selector start len) last hf hi hc fetched pcBound
  intro pc hpc
  have valid : index.val < exec.frames.val.length := List.getElem?_eq_some_iff.mp hf |>.1
  have lookup : (exec.frames.set index { raw with pc := pc }).val[index.val]? = some { raw with pc := pc } := by
    simp [alloc.vec.Vec.set_val_eq, valid]
  apply WP.spec_mono (dispatch_jump_table_exact memory hooks floats allocator
    { exec with frames := exec.frames.set index { raw with pc := pc } }
    store platform index {raw with pc := pc} inst compiled selector start len target value
    lookup hi hc bound input nonempty tableBound targetLookup)
  intro out effect
  obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
  have frames : (exec.frames.set index { raw with pc := pc }).set index { raw with pc := target } =
      exec.frames.set index { raw with pc := target } := by
    apply alloc.vec.Vec.ext
    simp only [alloc.vec.Vec.set_val_eq, List.set_set]
  simp only [frames] at exactState
  exact ⟨success, exactState, sameStore, samePlatform⟩

end Itasca.Runtime.Interp
