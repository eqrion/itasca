import Exec.Code.Local.Capacity.CallbackCapacity
import Exec.Code.Local.Lowering.Control.LoweringBranchIf

namespace Exec.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- An elided conditional branch needs one jump and its retained condition. -/
theorem branch_if_elided_loop_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 1)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop) (elided : frame.params = 0#u32 ∨ source = frame.height)
    (sourcePosition : source.val + frame.params.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    : runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  unfold runtime.compiler.control.FunctionCompiler.branch
  step as ⟨last, hlast⟩
  step as ⟨d, hd⟩
  step as ⟨actualIndex, hindex⟩
  have indexEq : actualIndex = index := by apply UScalar.eq_of_val_eq; simp [alloc.vec.Vec.len] at hlast; scalar_tac
  subst actualIndex
  have inBounds := (List.getElem?_eq_some_iff.mp lookup).1
  step as ⟨found, hfound⟩
  have foundEq : found = frame := by simpa [List.getElem?_eq_getElem inBounds, hfound] using lookup
  rw [foundEq]
  simp only [kind, bind_ok, Bool.false_eq_true, ite_false, ite_true]
  step as ⟨sum, hsum⟩
  cases sum with
  | none => simp at hsum; scalar_tac
  | some sum =>
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step as ⟨operand, hoperand⟩
    cases operand with
    | none => simp at hoperand; scalar_tac
    | some operand =>
      have sourceEq : operand = source := by apply UScalar.eq_of_val_eq; simp at hoperand; omega
      rw [sourceEq]
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        Bool.false_eq_true, ite_false, ite_true]
      step with compiler_condition ops compiler condition conditionAt as ⟨selected, selectedEq⟩
      subst selected
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have copyFalse : (if frame.params != 0#u32 then (Result.ok (source != frame.height) : Result Bool)
          else Result.ok false) = Result.ok false := by rcases elided with h | h <;> simp [h]
      rw [copyFalse]
      simp only [bind_ok, Bool.false_eq_true, ite_false, ite_true]
      step as ⟨current, back, hcurrent, hback⟩
      have currentEq : current = frame := by simpa [List.getElem?_eq_getElem inBounds, hcurrent] using lookup
      rw [currentEq]
      simp only [kind, bind_ok, uncurry_apply_pair, Bool.false_eq_true, ite_false, ite_true]
      let ready := {compiler with frames := back {frame with kind := .Loop}}
      have readyCapacity : CallbackCapacity ready state bound 1 := capacity.with_frames (back {frame with kind := .Loop})
      step with compiler_emit_available_effect ops bound available ready state (readyCapacity.one (by decide))
        (.JumpIfNonZero condition frame.start_pc) as ⟨status,afterJump,accepted,emission,jumpEffect⟩
      rw [accepted]
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
      exact ⟨trivial,jumpEffect⟩

/-- An elided conditional branch needs one jump and its retained condition. -/
theorem branch_if_elided_forward_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 1)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop) (elided : frame.results = 0#u32 ∨ source = frame.height)
    (sourcePosition : source.val + frame.results.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (fixupsCapacity : frame.fixups.length < Usize.max)
    (fixupsReserve : frame.fixups.length + 1 ≤ bound)
    : runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  cases kindEq : frame.kind
  all_goals try exact (forward kindEq).elim
  all_goals
    unfold runtime.compiler.control.FunctionCompiler.branch
    step as ⟨last, hlast⟩
    step as ⟨d, hd⟩
    step as ⟨actualIndex, hindex⟩
    have indexEq : actualIndex = index := by apply UScalar.eq_of_val_eq; simp [alloc.vec.Vec.len] at hlast; scalar_tac
    subst actualIndex
    have inBounds := (List.getElem?_eq_some_iff.mp lookup).1
    step as ⟨found, hfound⟩
    have foundEq : found = frame := by simpa [List.getElem?_eq_getElem inBounds, hfound] using lookup
    rw [foundEq]
    simp only [kindEq, bind_ok, Bool.false_eq_true, ite_false, ite_true]
    step as ⟨sum, hsum⟩
    cases sum with
    | none => simp at hsum; scalar_tac
    | some sum =>
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨operand, hoperand⟩
      cases operand with
      | none => simp at hoperand; scalar_tac
      | some operand =>
        have sourceEq : operand = source := by apply UScalar.eq_of_val_eq; simp at hoperand; omega
        rw [sourceEq]
        simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          Bool.false_eq_true, ite_false, ite_true]
        step with compiler_condition ops compiler condition conditionAt as ⟨selected, selectedEq⟩
        subst selected
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        have copyFalse : (if frame.results != 0#u32 then (Result.ok (source != frame.height) : Result Bool)
            else Result.ok false) = Result.ok false := by rcases elided with h | h <;> simp [h]
        rw [copyFalse]
        simp only [bind_ok, Bool.false_eq_true, ite_false, ite_true]
        step as ⟨current, back, hcurrent, hback⟩
        have currentEq : current = frame := by simpa [List.getElem?_eq_getElem inBounds, hcurrent] using lookup
        rw [currentEq]
        simp only [kindEq, bind_ok, uncurry_apply_pair, Bool.false_eq_true, ite_false, ite_true]
        step with budget_push_available ops bound available compiler.budget frame.fixups (alloc.vec.Vec.len compiler.function.code)
          fixupsCapacity fixupsReserve as ⟨status,budget,fixups,accepted,same,_⟩
        subst status budget
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,uncurry_apply_pair,Bool.false_eq_true,ite_false,ite_true]
        let ready := {compiler with frames := back {frame with end_reachable := true,fixups}}
        have readyCapacity : CallbackCapacity ready state bound 1 :=
          capacity.with_frames (back {frame with end_reachable := true,fixups})
        have emit := compiler_emit_available_effect ops bound available ready state (readyCapacity.one (by decide))
          (.JumpIfNonZero condition core.num.U32.MAX)
        simp only [ready,kindEq] at emit
        step with emit as ⟨status,afterJump,accepted,emission,jumpEffect⟩
        rw [accepted]
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
        exact ⟨trivial,jumpEffect⟩

end Exec.Code
