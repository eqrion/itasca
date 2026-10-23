import Exec.Interp.Control.PendingJump
import Exec.Interp.Relations.Regions
import Exec.Abs.Sim.Instruction

namespace Exec.Interp
open Aeneas Aeneas.Std

theorem JumpEffect.exact {before after : runtime.interp.Execution} {index : Usize}
    {raw : runtime.interp.Frame} {target : U32}
    (effect : JumpEffect before after index.val target)
    (lookup : before.frames.val[index.val]? = some raw) :
    after = { before with frames := before.frames.set index { raw with pc := target } } := by
  obtain ⟨found, foundAt, frames, unchanged⟩ := effect
  have same : found = raw := Option.some.inj (foundAt.symm.trans lookup)
  subst found
  have frameEq : after.frames = before.frames.set index { raw with pc := target } :=
    alloc.vec.Vec.ext _ _ (by simpa only [alloc.vec.Vec.set_val_eq] using frames)
  have exactState := congrArg (fun e : runtime.interp.Execution => { e with frames := after.frames }) unchanged
  change after = { before with frames := after.frames } at exactState
  simpa only [frameEq] using exactState

theorem dispatch_jumpIfZero_exact {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (cond target : U32) (value : Nat)
    (lookup : exec.frames.val[index.val]? = some raw)
    (bound : value < 2 ^ 32)
    (input : WordsAt exec.slots.val (raw.base.val + cond.val) [value]) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index
      raw.instance raw.function raw.base (.JumpIfZero cond target) ⦃ out => out.1 = .Ok () ∧
      out.2.1 = (if value = 0 then { exec with frames := exec.frames.set index { raw with pc := target } } else exec) ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  have frameBound : index.val < exec.frames.length := List.getElem?_eq_some_iff.mp lookup |>.1
  have slotBound : raw.base.val + cond.val < exec.slots.length := by simpa using (input 0 (by simp)).1
  have bits : exec.slots.val[raw.base.val + cond.val]!.val = value := by simpa using (input 0 (by simp)).2
  have cast : (UScalar.cast .U32 exec.slots.val[raw.base.val + cond.val]!).val = value := by
    simp only [UScalar.cast_val_eq, UScalarTy.numBits, bits, Nat.mod_eq_of_lt bound]
  have zero : UScalar.cast .U32 exec.slots.val[raw.base.val + cond.val]! = 0#u32 ↔ value = 0 := by scalar_tac
  simp only [runtime.interp.dispatch]
  obtain ⟨out, result, success, effect⟩ := WP.spec_imp_exists
    (jump_if_zero_effect exec index raw.base cond target frameBound slotBound)
  simp only [zero] at effect
  have exactState : out.2 = (if value = 0 then { exec with frames := exec.frames.set index { raw with pc := target } } else exec) := by
    by_cases equal : value = 0
    · simp only [if_pos equal] at effect ⊢
      exact effect.exact lookup
    · simpa only [if_neg equal] using effect
  rw [result, bind_ok]
  rcases out with ⟨answer, nextExec⟩
  with_unfolding_all apply WP.spec.ret
  exact ⟨success, exactState, rfl, rfl⟩

/-- A guarded branch with an operand transfer first removes its condition.
The false path skips the transfer/jump pair; the true path reaches BR. -/
theorem dispatch_branchGuard_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (cond target : U32) (value : Nat)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (depth : Nat) (front : List val)
    (lookup : exec.frames.val[index.val]? = some raw)
    (bound : value < 2 ^ 32)
    (position : cond.val = Code.slots ((f.locals ++ front).map Code.valueType))
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ [Abs.integerVal .I32 value] } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ [Abs.integerVal .I32 value] }) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index
      raw.instance raw.function raw.base (.JumpIfZero cond target) ⦃ out => out.1 = .Ok () ∧
      out.2.1 = (if value = 0 then { exec with frames := exec.frames.set index { raw with pc := target } } else exec) ∧
      FrameSlots out.2.1 raw { f with code := if value = 0 then after else .BR (.mk_uN depth) :: after, vals := front } ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      Abs.NextSim
        ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ [Abs.integerVal .I32 value] } :: rest, []⟩
        ⟨s, ambient, { f with code := if value = 0 then after else .BR (.mk_uN depth) :: after, vals := front } :: rest, []⟩ ⦄ := by
  have allValues : ValuesAt exec.slots.val raw.base.val ((f.locals ++ front) ++ [Abs.integerVal .I32 value]) := by
    simpa only [FrameSlots, List.append_assoc] using slots
  have input : WordsAt exec.slots.val (raw.base.val + cond.val) [value] := by
    simpa only [position, ValuesAt, Code.encodeValues, List.flatMap_cons, List.flatMap_nil,
      Abs.integerVal, Code.encodeValue, List.append_nil] using allValues.operands
  have step : Abs.astep
      ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ [Abs.integerVal .I32 value] } :: rest, []⟩ = .next
      ⟨s, ambient, { f with code := if value = 0 then after else .BR (.mk_uN depth) :: after, vals := front } :: rest, []⟩ := by
    have hb : value < 4294967296 := bound
    simp [Abs.astep, Abs.pop_append, Abs.integerVal, Abs.integer, numtype_Inn, hb, Abs.advance]
  have simulation := Abs.instruction_simulation s ambient { f with vals := front ++ [Abs.integerVal .I32 value] } rest
    (.BR_IF (.mk_uN depth)) after _ (.br_if _) typed step
  apply WP.spec_mono (dispatch_jumpIfZero_exact memory hooks floats allocator exec store platform index raw cond target value lookup bound input)
  intro out effect
  obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
  refine ⟨success, exactState, ?_, sameStore, samePlatform, simulation⟩
  rw [exactState]
  split <;> exact allValues.locals

theorem dispatch_jumpIfNonZero_exact {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (cond target : U32) (value : Nat)
    (lookup : exec.frames.val[index.val]? = some raw)
    (bound : value < 2 ^ 32)
    (input : WordsAt exec.slots.val (raw.base.val + cond.val) [value]) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index
      raw.instance raw.function raw.base (.JumpIfNonZero cond target) ⦃ out => out.1 = .Ok () ∧
      out.2.1 = (if value = 0 then exec else { exec with frames := exec.frames.set index { raw with pc := target } }) ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  have frameBound : index.val < exec.frames.length := List.getElem?_eq_some_iff.mp lookup |>.1
  have slotBound : raw.base.val + cond.val < exec.slots.length := by simpa using (input 0 (by simp)).1
  have bits : exec.slots.val[raw.base.val + cond.val]!.val = value := by simpa using (input 0 (by simp)).2
  have cast : (UScalar.cast .U32 exec.slots.val[raw.base.val + cond.val]!).val = value := by
    simp only [UScalar.cast_val_eq, UScalarTy.numBits, bits, Nat.mod_eq_of_lt bound]
  have zero : UScalar.cast .U32 exec.slots.val[raw.base.val + cond.val]! = 0#u32 ↔ value = 0 := by scalar_tac
  simp only [runtime.interp.dispatch]
  obtain ⟨out, result, success, effect⟩ := WP.spec_imp_exists
    (jump_if_non_zero_effect exec index raw.base cond target frameBound slotBound)
  simp only [zero] at effect
  have exactState : out.2 = (if value = 0 then exec else { exec with frames := exec.frames.set index { raw with pc := target } }) := by
    by_cases equal : value = 0
    · simp only [if_pos equal] at effect ⊢
      exact effect
    · simp only [if_neg equal] at effect ⊢
      exact effect.exact lookup
  rw [result, bind_ok]
  rcases out with ⟨answer, nextExec⟩
  with_unfolding_all apply WP.spec.ret
  exact ⟨success, exactState, rfl, rfl⟩


end Exec.Interp
