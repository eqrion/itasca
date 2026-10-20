import Exec.Code.Local.Capacity.TransferAvailability
import Exec.Code.Local.Capacity.CallbackCapacity
import Exec.Code.Local.Lowering.Control.LoweringLoopBranch

namespace Exec.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- A nonelided backward branch accepts with independently reserved capacity
for its transfer and jump. Its source argument coordinates justify arithmetic. -/
theorem branch_transfer_loop_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 2)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop) (nonempty : frame.params ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.params.val + skip.val = compiler.height.val) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 2 else 0) ⦄ := by
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
        Bool.false_eq_true, ite_false, bne_iff_ne, nonempty, different, ite_true]
      rw [if_pos nonempty]
      simp only [bind_ok, bne_iff_ne, if_pos different]
      step with compiler_transfer_available ops law bound available compiler state (capacity.one (by decide))
        frame.height source frame.params nonempty different as ⟨status,afterCopy,accepted,emission,copyEffect⟩
      rw [accepted]
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      have afterCopyCapacity : CallbackCapacity afterCopy state bound 1 := capacity.after_emission emission copyEffect
      obtain ⟨copyBudget,copyCode,copyOffsets,rfl,copiedCode,copiedOffsets⟩ := emission
      step as ⟨current,back,hcurrent,hback⟩
      have currentEq : current = frame := by simpa [List.getElem?_eq_getElem inBounds,hcurrent] using lookup
      rw [currentEq]
      simp only [kind,bind_ok,uncurry_apply_pair,Bool.false_eq_true,ite_false,ite_true]
      let copied := {compiler with
        budget := copyBudget
        function := {compiler.function with code := copyCode,source_offsets := copyOffsets}}
      let ready := {copied with frames := back {frame with kind := .Loop}}
      have readyCapacity : CallbackCapacity ready state bound 1 :=
        afterCopyCapacity.with_frames (back {frame with kind := .Loop})
      step with compiler_emit_available_effect ops bound available ready state (readyCapacity.one (by decide))
        (.Jump frame.start_pc) as ⟨status,afterJump,accepted,emission,jumpEffect⟩
      rw [accepted]
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
      exact ⟨trivial,(copyEffect.trans jumpEffect).weaken (by intro counter; cases counter <;> simp)⟩

/-- Empty and identity loop transfers elide the copy and need only the jump. -/
theorem branch_elided_loop_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 1)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop) (elided : frame.params = 0#u32 ∨ source = frame.height)
    (sourcePosition : source.val + frame.params.val + skip.val = compiler.height.val) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false ⦃ out =>
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
        Bool.false_eq_true, ite_false]
      have copyFalse : (if frame.params != 0#u32 then (Result.ok (source != frame.height) : Result Bool)
          else Result.ok false) = Result.ok false := by rcases elided with h | h <;> simp [h]
      rw [copyFalse]
      simp only [bind_ok, Bool.false_eq_true, ite_false]
      step as ⟨current, back, hcurrent, hback⟩
      have currentEq : current = frame := by simpa [List.getElem?_eq_getElem inBounds, hcurrent] using lookup
      rw [currentEq]
      simp only [kind, bind_ok, uncurry_apply_pair, Bool.false_eq_true, ite_false, ite_true]
      let ready := {compiler with frames := back {frame with kind := .Loop}}
      have readyCapacity : CallbackCapacity ready state bound 1 :=
        capacity.with_frames (back {frame with kind := .Loop})
      step with compiler_emit_available_effect ops bound available ready state (readyCapacity.one (by decide))
        (.Jump frame.start_pc) as ⟨status,afterJump,accepted,emission,jumpEffect⟩
      rw [accepted]
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
      exact ⟨trivial,jumpEffect⟩

/-- Every unconditional backward branch accepts from its source parameter
width, with at most two instructions and no other budget charge. -/
theorem compiler_branch_loop_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 2)
    (frame : runtime.compiler.Frame) (index : Usize) (depth skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop) (widthFits : frame.params.val + skip.val ≤ compiler.height.val) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 2 else 0) ⦄ := by
  let source : U32 := UScalar.ofNatCore (compiler.height.val-(frame.params.val+skip.val)) (by scalar_tac)
  have sourcePosition : source.val + frame.params.val + skip.val = compiler.height.val := by
    change compiler.height.val-(frame.params.val+skip.val)+frame.params.val+skip.val = compiler.height.val
    omega
  by_cases elided : frame.params = 0#u32 ∨ source = frame.height
  · apply WP.spec_mono (branch_elided_loop_available ops bound available compiler state (capacity.mono (by decide))
      frame index depth source skip lookup position kind elided sourcePosition)
    intro out post
    exact ⟨post.1,post.2.weaken (by intro counter; cases counter <;> simp)⟩
  · exact branch_transfer_loop_available ops law bound available compiler state capacity frame index depth source skip
      lookup position kind (by intro empty; exact elided (Or.inl empty))
      (by intro same; exact elided (Or.inr same)) sourcePosition

end Exec.Code
