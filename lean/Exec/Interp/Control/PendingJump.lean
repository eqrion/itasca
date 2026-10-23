import Exec.Interp.Relations.Fetch
import Exec.Interp.Relations.Rel

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- During a branch's second instruction the abstract transfer has already
happened. The current bytecode must be the retained unconditional jump, and its
target must carry the source continuation certificate. -/
structure PendingLinearJump (raw : runtime.interp.Frame) (source : Abs.AFrame)
    (compiled : runtime.bytecode.CompiledFunction) (target : U32)
    (next : Nat) (output : List valtype) : Prop where
  fetched : compiled.code.val[raw.pc.val]? = some (.Jump target)
  continuation : LinearPoint { raw with pc := target } source compiled next output

/-- Administrative potential covers source constants, forward skip jumps,
and the second half of a branch, including backward loop targets. The pending
phase weighs more than any possible remaining instruction distance. -/
def dispatchMeasure (pending : Bool) (codeLength pc : Nat) (state : Abs.AState) : Nat :=
  Abs.administrativeMeasure state * (2 * (codeLength + 1)) +
    (if pending then codeLength + 1 else 0) + (codeLength - pc)

theorem dispatchMeasure_jump (state : Abs.AState) (codeLength pc target : Nat) :
    dispatchMeasure false codeLength target state < dispatchMeasure true codeLength pc state := by
  simp only [dispatchMeasure, Bool.false_eq_true, ite_false, ite_true]
  omega

theorem dispatchMeasure_forward (state : Abs.AState) (codeLength pc target : Nat)
    (forward : pc < target) (bound : target ≤ codeLength) :
    dispatchMeasure false codeLength target state < dispatchMeasure false codeLength pc state := by
  simp only [dispatchMeasure, Bool.false_eq_true, ite_false]
  omega

theorem dispatchMeasure_source {before after : Abs.AState}
    (codeLength pc target : Nat)
    (decrease : Abs.administrativeMeasure after < Abs.administrativeMeasure before) :
    dispatchMeasure false codeLength target after < dispatchMeasure false codeLength pc before := by
  have adjacent : Abs.administrativeMeasure after + 1 ≤ Abs.administrativeMeasure before := decrease
  have multiplied := Nat.mul_le_mul_right (2 * (codeLength + 1)) adjacent
  simp only [Nat.add_mul, Nat.one_mul] at multiplied
  simp only [dispatchMeasure, Bool.false_eq_true, ite_false]
  omega

theorem dispatchMeasure_bounded (pending : Bool) (codeLength pc : Nat) (state : Abs.AState) (bound : Nat)
    (bounded : Abs.administrativeMeasure state ≤ bound) :
    dispatchMeasure pending codeLength pc state ≤ bound * (2 * (codeLength + 1)) + 2 * codeLength + 1 := by
  have multiplied := Nat.mul_le_mul_right (2 * (codeLength + 1)) bounded
  cases pending <;> simp only [dispatchMeasure, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem dispatch_jump_exact {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index inst function base : Usize) (raw : runtime.interp.Frame) (target : U32)
    (lookup : exec.frames.val[index.val]? = some raw) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (.Jump target) ⦃ out => out.1 = .Ok () ∧
        out.2.1 = { exec with frames := exec.frames.set index { raw with pc := target } } ∧
        out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  have bound : index.val < exec.frames.length := List.getElem?_eq_some_iff.mp lookup |>.1
  simp only [runtime.interp.dispatch]
  obtain ⟨out, result, success, found, foundAt, frames, unchanged⟩ := WP.spec_imp_exists
    (jump_effect exec index target bound)
  have same : found = raw := Option.some.inj (foundAt.symm.trans lookup)
  subst found
  have frameEq : out.2.frames = exec.frames.set index { raw with pc := target } :=
    alloc.vec.Vec.ext _ _ (by simpa only [alloc.vec.Vec.set_val_eq] using frames)
  have exactState := congrArg (fun e : runtime.interp.Execution => { e with frames := out.2.frames }) unchanged
  change out.2 = { exec with frames := out.2.frames } at exactState
  rw [frameEq] at exactState
  rw [result, bind_ok]
  rcases out with ⟨answer, nextExec⟩
  with_unfolding_all apply WP.spec.ret
  exact ⟨success, exactState, rfl, rfl⟩

theorem step_jump_exact {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (target : U32)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (fetched : compiled.code.val[raw.pc.val]? = some (.Jump target)) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧
      out.2.1 = { exec with frames := exec.frames.set index { raw with pc := target } } ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
    (.Jump target) last hf hi hc fetched pcBound
  intro pc hpc
  have valid : index.val < exec.frames.val.length := List.getElem?_eq_some_iff.mp hf |>.1
  have lookup : (exec.frames.set index { raw with pc := pc }).val[index.val]? = some { raw with pc := pc } := by
    simp [alloc.vec.Vec.set_val_eq, valid]
  apply WP.spec_mono (dispatch_jump_exact memory hooks floats allocator
    { exec with frames := exec.frames.set index { raw with pc := pc } }
    store platform index raw.instance raw.function raw.base { raw with pc := pc } target lookup)
  intro out effect
  obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
  have frames : (exec.frames.set index { raw with pc := pc }).set index { raw with pc := target } =
      exec.frames.set index { raw with pc := target } := by
    apply alloc.vec.Vec.ext
    simp only [alloc.vec.Vec.set_val_eq, List.set_set]
  simp only [frames] at exactState
  exact ⟨success, exactState, sameStore, samePlatform⟩


theorem step_pendingJump_certified {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (target : U32) (next : Nat) (output : List valtype) (source : Abs.AFrame)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (slots : FrameSlots exec raw source)
    (pending : PendingLinearJump raw source compiled target next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧
      out.2.1 = { exec with frames := exec.frames.set index { raw with pc := target } } ∧
      FrameSlots out.2.1 { raw with pc := target } source ∧
      LinearPoint { raw with pc := target } source compiled next output ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
    (.Jump target) last hf hi hc pending.fetched pcBound
  intro pc hpc
  have valid : index.val < exec.frames.val.length := List.getElem?_eq_some_iff.mp hf |>.1
  have lookup : (exec.frames.set index { raw with pc := pc }).val[index.val]? = some { raw with pc := pc } := by
    simp [alloc.vec.Vec.set_val_eq, valid]
  apply WP.spec_mono (dispatch_jump_exact memory hooks floats allocator
    { exec with frames := exec.frames.set index { raw with pc := pc } }
    store platform index raw.instance raw.function raw.base { raw with pc := pc } target lookup)
  intro out effect
  obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
  have frames : (exec.frames.set index { raw with pc := pc }).set index { raw with pc := target } =
      exec.frames.set index { raw with pc := target } := by
    apply alloc.vec.Vec.ext
    simp only [alloc.vec.Vec.set_val_eq, List.set_set]
  simp only [frames] at exactState
  refine ⟨success, exactState, ?_, pending.continuation, sameStore, samePlatform⟩
  rw [exactState]
  exact slots

end Exec.Interp
