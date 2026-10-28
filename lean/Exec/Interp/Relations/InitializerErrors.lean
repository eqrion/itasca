import Exec.Interp.Relations.InitializerResolution
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem synthetic_initializer_errors (law : Platform.AllocCorrect allocator)
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
        (∀ pair, out.1 = .Ok pair → pair = ((words[0]?).getD 0#u64, (words[1]?).getD 0#u64)) ∧
        (∀ error, out.1 = .Err error → ∃ resource, error = .Exhausted resource) ⦄ := by
  unfold runtime.interp.run_synthetic
  step with vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  step with vec_index_given inst.module.functions function code hc as ⟨found, hfound⟩
  subst found
  simp only [lift, bind_ok, runtime.interp.Execution.new]
  step with ensure_effect allocator law _ _ _ as ⟨status, prepared, ensured⟩
  cases status with
  | Err error =>
    have exhausted : ∃ resource, error = .Exhausted resource := by
      cases error <;> simp_all only [EnsureEffect]
      rename_i resource
      exact ⟨resource, rfl⟩
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using exhausted
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

theorem synthetic_resolved_initializer_errors (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (expr : Itasca.types.ConstExpr) (ty : Itasca.types.ValueType) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Code.InitializerCode code expr ty)
    (resolved : InitializerResolution store inst expr ty words) :
    runtime.interp.run_synthetic memory hooks floats allocator store platform instIndex function
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧
        (∀ pair, out.1 = .Ok pair → pair = ((words[0]?).getD 0#u64, (words[1]?).getD 0#u64)) ∧
        (∀ error, out.1 = .Err error → ∃ resource, error = .Exhausted resource) ⦄ := by
  obtain ⟨instruction, hop, hcode⟩ := compiled.code
  apply synthetic_initializer_errors memory hooks floats allocator law store platform instIndex function
    inst code instruction words hi hc (resolved.read code instruction hop)
    (by rw [compiled.capacity]; exact resolved.width)
  simpa [compiled.capacity] using hcode

end Itasca.Runtime.Interp
