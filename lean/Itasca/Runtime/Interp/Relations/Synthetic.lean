import Itasca.Runtime.Interp.Relations.Initializer

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem synthetic_loop_initializer (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (words : List U64) (width : U32)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (read : InitialRead store inst code instruction words)
    (capacity : words.length ≤ exec.slots.length)
    (returnCapacity : width.val ≤ exec.slots.length)
    (hf : exec.frames.val = [initializerFrame instIndex function 0#u32])
    (hcode : code.code.val = [instruction, .Return 0#u32 width]) :
    runtime.interp.run_synthetic_loop memory hooks floats allocator store platform exec (.Ok ())
      ⦃ out => out.1 = store ∧ out.2.1 = platform ∧
        out.2.2.1.val = initialSlots exec.slots.val words ∧ out.2.2.2 = .Ok () ⦄ := by
  obtain ⟨⟨status1, exec1, store1, platform1⟩, first, hok1, slots1, frames1, hs1, hp1⟩ :=
    WP.spec_imp_exists (step_initial_read memory hooks floats allocator exec store platform
      instIndex function inst code instruction words hi hc read capacity hf (by simp [hcode]))
  dsimp only at hok1 slots1 frames1 hs1 hp1
  subst status1 store1 platform1
  have capacity1 : width.val ≤ exec1.slots.length := by
    change width.val ≤ exec1.slots.val.length
    rw [slots1, initial_slots_length]
    exact returnCapacity
  obtain ⟨⟨status2, exec2, store2, platform2⟩, second, hok2, slots2, frames2, hs2, hp2⟩ :=
    WP.spec_imp_exists (step_initial_return memory hooks floats allocator exec1 store platform
      instIndex function inst code width hi hc capacity1 frames1 (by simp [hcode]))
  dsimp only at hok2 slots2 frames2 hs2 hp2
  subst status2 store2 platform2
  have active0 : 0 < exec.frames.length := by simp [alloc.vec.Vec.length, hf]
  have active1 : 0 < exec1.frames.length := by simp [alloc.vec.Vec.length, frames1]
  have body0 := synthetic_body_active memory hooks floats allocator exec store platform active0
  have body1 := synthetic_body_active memory hooks floats allocator exec1 store platform active1
  rw [first, bind_ok] at body0
  rw [second, bind_ok] at body1
  have body2 := synthetic_body_done memory hooks floats allocator exec2 store platform frames2
  have trace : NormalTrace (fun state : runtime.store.Store M × P × runtime.interp.Execution ×
      core.result.Result Unit runtime.ExecError =>
      runtime.interp.run_synthetic_loop.body memory hooks floats allocator state.1 state.2.1
        state.2.2.1 state.2.2.2) 2
      (store, platform, exec, .Ok ()) (store, platform, exec2.slots, .Ok ()) :=
    .next body0 (.next body1 (.done body2))
  change loop _ _ ⦃ _ ⦄
  rw [trace.result]
  simp [WP.spec_ok, slots2, slots1]

@[step] theorem get_effect (slots : Slice U64) (position : Usize) :
    runtime.interp.get slots position ⦃ value =>
      value = (slots.val[position.val]?).getD 0#u64 ⦄ := by
  unfold runtime.interp.get
  dsimp only
  split
  · rename_i inside
    step as ⟨value, hvalue⟩
    have bound : position.val < slots.val.length := by scalar_tac
    simp [List.getElem?_eq_getElem bound, hvalue]
  · rename_i outside
    have bound : slots.val.length ≤ position.val := by scalar_tac
    simp [List.getElem?_eq_none bound]

theorem InitialRead.zero_slots {store : runtime.store.Store M} {inst code instruction words}
    (read : InitialRead store inst code instruction words) :
    initialSlots (List.replicate words.length 0#u64) words = words := by
  cases read <;> simp [initialSlots]

/-- The complete extracted synthetic entry point terminates for a resolved
constant initializer. Allocation failure is permitted; every result preserves
the raw Store and platform exactly. Successful results are the resolved words. -/
theorem synthetic_initializer (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (read : InitialRead store inst code instruction words)
    (width : code.slot_count.val = words.length)
    (hcode : code.code.val = [instruction, .Return 0#u32 code.slot_count]) :
    runtime.interp.run_synthetic memory hooks floats allocator store platform instIndex function
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧
        ∀ pair, out.1 = .Ok pair → pair = ((words[0]?).getD 0#u64, (words[1]?).getD 0#u64) ⦄ := by
  unfold runtime.interp.run_synthetic
  step with vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  step with vec_index_given inst.module.functions function code hc as ⟨found, hfound⟩
  subst found
  simp only [lift, bind_ok, runtime.interp.Execution.new]
  step with ensure_effect allocator law _ _ _ as ⟨status, prepared, ensured⟩
  cases status with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok unit =>
    cases unit
    simp only [EnsureEffect] at ensured
    obtain ⟨limit, hslots, hother⟩ := ensured
    have slots : prepared.slots.val = List.replicate words.length 0#u64 := by
      simpa [alloc.vec.Vec.new, width] using hslots
    have frames : prepared.frames.val = [] := by
      have h := congrArg runtime.interp.Execution.frames hother
      simpa [alloc.vec.Vec.new] using congrArg alloc.vec.Vec.val h
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨answer, reserved⟩ := law.reserve_eq prepared.frames 1#usize
    have reserveCall : runtime.reserve allocator prepared.frames 1#usize = .ok
        ((if answer then .Ok () else .Err (.Exhausted .Allocation)), prepared.frames) := by
      cases answer <;> simp [runtime.reserve, reserved]
    rw [reserveCall, bind_ok]
    cases answer with
    | false =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | true =>
      simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨pushed, hpushed⟩
      have pushedFrames : pushed.val = [initializerFrame instIndex function 0#u32] := by
        simpa [frames, initializerFrame] using hpushed
      have capacity : words.length ≤ prepared.slots.length := by
        simp [alloc.vec.Vec.length, slots]
      step with synthetic_loop_initializer memory hooks floats allocator
        { prepared with frames := pushed } store platform instIndex function inst code instruction words
        code.slot_count hi hc read capacity (by simpa [width] using capacity) pushedFrames hcode
        as ⟨store', platform', finalSlots, result, hs, hp, hwords, hok⟩
      subst store' platform' result
      have finalWords : finalSlots.val = words := by
        rw [slots, read.zero_slots] at hwords
        exact hwords
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with get_effect finalSlots.deref 0#usize as ⟨lo, hlo⟩
      step with get_effect finalSlots.deref 1#usize as ⟨hi, hhi⟩
      have low : lo = (words[0]?).getD 0#u64 := by simpa [alloc.vec.Vec.deref, finalWords] using hlo
      have high : hi = (words[1]?).getD 0#u64 := by simpa [alloc.vec.Vec.deref, finalWords] using hhi
      simp [low, high]

end Itasca.Runtime.Interp
