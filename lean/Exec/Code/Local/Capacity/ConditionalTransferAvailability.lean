import Exec.Code.Local.Capacity.TransferAvailability
import Exec.Code.Local.Capacity.CallbackCapacity
import Exec.Code.Local.Lowering.Common.LoweringConditionalTransfer

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem emitted_last {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction} (emitted : Emitted before after instruction) :
    after.function.code.val[before.function.code.val.length]? = some instruction := by
  obtain ⟨budget,code,sources,frame,appended,_⟩ := emitted
  rw [frame,appended]
  simp

/-- A conditional backward transfer accepts its guard, copy, jump, and guard
patch from three reserved instruction units and independent source coordinates. -/
theorem branch_if_transfer_loop_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 3)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kindEq : frame.kind = .Loop) (nonempty : frame.params ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.params.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 3 else 0) ⦄ := by
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
      have copyTrue : (if frame.params != 0#u32 then (Result.ok (source != frame.height) : Result Bool)
          else Result.ok false) = Result.ok true := by simp [nonempty, different]
      rw [copyTrue]
      simp only [bind_ok, Bool.false_eq_true, ite_false, ite_true]
      step with compiler_emit_available_effect ops bound available compiler state (capacity.one (by decide))
        (.JumpIfZero condition core.num.U32.MAX) as ⟨status,guarded,accepted,guardEmission,guardEffect⟩
      rw [accepted]
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      have guardCapacity : CallbackCapacity guarded state bound 2 := capacity.after_emission guardEmission guardEffect
      have guardLookup := emitted_last guardEmission
      obtain ⟨guardBudget,guardCode,guardOffsets,rfl,guardedCode,guardedOffsets⟩ := guardEmission
      let guarded := {compiler with
        budget := guardBudget
        function := {compiler.function with code := guardCode,source_offsets := guardOffsets}}
      step with compiler_transfer_available ops law bound available guarded state (guardCapacity.one (by decide))
        frame.height source frame.params nonempty different as ⟨status,afterCopy,accepted,copyEmission,copyEffect⟩
      rw [accepted]
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      have copyCapacity : CallbackCapacity afterCopy state bound 1 := guardCapacity.after_emission copyEmission copyEffect
      have copiedGuard := copyEmission.old_instruction guardLookup
      obtain ⟨copyBudget,copyCode,copyOffsets,rfl,copiedCode,copiedOffsets⟩ := copyEmission
      step as ⟨current,back,hcurrent,hback⟩
      have currentEq : current = frame := by simpa [List.getElem?_eq_getElem inBounds,hcurrent] using lookup
      rw [currentEq]
      simp only [kindEq,bind_ok,uncurry_apply_pair,Bool.false_eq_true,ite_false,ite_true]
      let copied := {guarded with
        budget := copyBudget
        function := {guarded.function with code := copyCode,source_offsets := copyOffsets}}
      let ready := {copied with frames := back {frame with kind := .Loop}}
      have readyCapacity : CallbackCapacity ready state bound 1 := copyCapacity.with_frames (back {frame with kind := .Loop})
      have emit := compiler_emit_available_effect ops bound available ready state (readyCapacity.one (by decide))
        (.Jump frame.start_pc)
      simp only [ready,copied,guarded,kindEq] at emit
      step with emit as ⟨status,afterJump,accepted,jumpEmission,jumpEffect⟩
      rw [accepted]
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      have finalCapacity : CallbackCapacity afterJump state bound 0 := readyCapacity.after_emission jumpEmission jumpEffect
      have retained : afterJump.function.code.val[compiler.function.code.val.length]? =
          some (.JumpIfZero condition core.num.U32.MAX) := jumpEmission.old_instruction copiedGuard
      step with compiler_pc_available ops afterJump (by have room := finalCapacity.pc; simpa using room)
        as ⟨status,current,same,resume,accepted,_⟩
      subst current
      rw [accepted]
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      step with compiler_patch ops afterJump (alloc.vec.Vec.len compiler.function.code) (.zero condition)
        core.num.U32.MAX resume retained as ⟨status,patched,statusEq,patchedShape⟩
      subst status
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
      obtain ⟨newCode,patchedEq,_⟩ := patchedShape
      refine ⟨trivial,?_⟩
      rw [patchedEq]
      exact ((guardEffect.trans copyEffect).trans jumpEffect).weaken (by intro counter; cases counter <;> simp)


/-- A conditional forward transfer accepts its guard, copy, jump, and guard
patch from three reserved instruction units and independent source coordinates. -/
theorem branch_if_transfer_forward_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 3)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop) (nonempty : frame.results ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.results.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (fixupsCapacity : frame.fixups.length < Usize.max)
    (fixupsReserve : frame.fixups.length + 1 ≤ bound) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 3 else 0) ⦄ := by
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
    simp only [kindEq, bind_ok, Bool.false_eq_true, ite_false]
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
        have copyTrue : (if frame.results != 0#u32 then (Result.ok (source != frame.height) : Result Bool)
            else Result.ok false) = Result.ok true := by simp [nonempty, different]
        rw [copyTrue]
        simp only [bind_ok, Bool.false_eq_true, ite_false, ite_true]
        step with compiler_emit_available_effect ops bound available compiler state (capacity.one (by decide))
          (.JumpIfZero condition core.num.U32.MAX) as ⟨status,guarded,accepted,guardEmission,guardEffect⟩
        rw [accepted]
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
        have guardCapacity : CallbackCapacity guarded state bound 2 := capacity.after_emission guardEmission guardEffect
        have guardLookup := emitted_last guardEmission
        obtain ⟨guardBudget,guardCode,guardOffsets,rfl,guardedCode,guardedOffsets⟩ := guardEmission
        let guarded := {compiler with
          budget := guardBudget
          function := {compiler.function with code := guardCode,source_offsets := guardOffsets}}
        step with compiler_transfer_available ops law bound available guarded state (guardCapacity.one (by decide))
          frame.height source frame.results nonempty different as ⟨status,afterCopy,accepted,copyEmission,copyEffect⟩
        rw [accepted]
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
        have copyCapacity : CallbackCapacity afterCopy state bound 1 := guardCapacity.after_emission copyEmission copyEffect
        have copiedGuard := copyEmission.old_instruction guardLookup
        obtain ⟨copyBudget,copyCode,copyOffsets,rfl,copiedCode,copiedOffsets⟩ := copyEmission
        step as ⟨current,back,hcurrent,hback⟩
        have currentEq : current = frame := by simpa [List.getElem?_eq_getElem inBounds,hcurrent] using lookup
        rw [currentEq]
        simp only [kindEq,bind_ok,uncurry_apply_pair,Bool.false_eq_true,ite_false,ite_true]
        step with budget_push_available ops bound available copyBudget frame.fixups (alloc.vec.Vec.len copyCode)
          fixupsCapacity fixupsReserve as ⟨status,budget,fixups,accepted,same,_⟩
        subst status budget
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,uncurry_apply_pair,Bool.false_eq_true,ite_false,ite_true]
        let copied := {guarded with
          budget := copyBudget
          function := {guarded.function with code := copyCode,source_offsets := copyOffsets}}
        let ready := {copied with frames := back {frame with end_reachable := true,fixups}}
        have readyCapacity : CallbackCapacity ready state bound 1 := copyCapacity.with_frames (back {frame with end_reachable := true,fixups})
        have emit := compiler_emit_available_effect ops bound available ready state (readyCapacity.one (by decide))
          (.Jump core.num.U32.MAX)
        simp only [ready,copied,guarded,kindEq] at emit readyCapacity
        step with emit as ⟨status,afterJump,accepted,jumpEmission,jumpEffect⟩
        rw [accepted]
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
        have finalCapacity : CallbackCapacity afterJump state bound 0 := readyCapacity.after_emission jumpEmission jumpEffect
        have retained : afterJump.function.code.val[compiler.function.code.val.length]? =
            some (.JumpIfZero condition core.num.U32.MAX) := jumpEmission.old_instruction copiedGuard
        step with compiler_pc_available ops afterJump (by have room := finalCapacity.pc; simpa using room)
          as ⟨status,current,same,resume,accepted,_⟩
        subst current
        rw [accepted]
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
        step with compiler_patch ops afterJump (alloc.vec.Vec.len compiler.function.code) (.zero condition)
          core.num.U32.MAX resume retained as ⟨status,patched,statusEq,patchedShape⟩
        subst status
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
        obtain ⟨newCode,patchedEq,_⟩ := patchedShape
        refine ⟨trivial,?_⟩
        rw [patchedEq]
        exact ((guardEffect.trans copyEffect).trans jumpEffect).weaken (by intro counter; cases counter <;> simp)

end Itasca.Runtime.Code
