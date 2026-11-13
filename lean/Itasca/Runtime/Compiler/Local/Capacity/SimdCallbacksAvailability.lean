import Itasca.Runtime.Compiler.Local.Capacity.UnreachableAvailability
import Itasca.Runtime.Compiler.Local.Lowering.Control.LoweringTrap
import Itasca.Runtime.Compiler.Local.Capacity.CallAvailability
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdMeaningCounts
import Mathlib.Tactic.IntervalCases
import Itasca.Runtime.Compiler.Local.Capacity.GlobalAvailability
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdOpcodeReduction
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdDispatch
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdBitsCallbacks

/-!
Sections, each formerly its own module: ConditionalBranchAvailability, ElseDispatchAvailability, SimdOpAvailability, SimdCallbacksAvailability.
-/

/-! ## ConditionalBranchAvailability -/

section

/-!
Allocator availability for elided and emitted conditional branches, composed into successful callback replay.
-/

/-! ## Conditional Elided Availability -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## Conditional Transfer Availability -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## Conditional Branch Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Conditional branches accept at every label depth and kind with at most
three instructions. Widths and the condition coordinate are source-layout
premises; the resume PC is constructed by the actual checked lowering. -/
theorem compiler_conditional_branch_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 3)
    (frame : runtime.compiler.Frame) (index : Usize) (depth condition : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (widthFits : (match frame.kind with | .Loop => frame.params | _ => frame.results).val + 1 ≤ compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (fixupsCapacity : frame.fixups.length < Usize.max)
    (fixupsReserve : frame.fixups.length + 1 ≤ bound) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 3 else 0) ⦄ := by
  by_cases loopEntry : frame.kind = .Loop
  · have enough : frame.params.val + 1 ≤ compiler.height.val := by simpa only [loopEntry] using widthFits
    let source : U32 := UScalar.ofNatCore (compiler.height.val-(frame.params.val+1)) (by scalar_tac)
    have sourcePosition : source.val + frame.params.val + 1 = compiler.height.val := by
      change compiler.height.val-(frame.params.val+1)+frame.params.val+1 = compiler.height.val
      omega
    by_cases elided : frame.params = 0#u32 ∨ source = frame.height
    · apply WP.spec_mono (branch_if_elided_loop_available ops bound available compiler state (capacity.mono (by decide))
        frame index depth source condition lookup position loopEntry elided sourcePosition conditionAt)
      intro out post
      exact ⟨post.1,post.2.weaken (by intro counter; cases counter <;> simp)⟩
    · exact branch_if_transfer_loop_available ops law bound available compiler state capacity frame index depth source condition
        lookup position loopEntry (by intro zero; exact elided (.inl zero))
        (by intro same; exact elided (.inr same)) sourcePosition conditionAt
  · have enough : frame.results.val + 1 ≤ compiler.height.val := by
      cases kindEq : frame.kind
      all_goals first | exact False.elim (loopEntry kindEq) | simpa only [kindEq] using widthFits
    let source : U32 := UScalar.ofNatCore (compiler.height.val-(frame.results.val+1)) (by scalar_tac)
    have sourcePosition : source.val + frame.results.val + 1 = compiler.height.val := by
      change compiler.height.val-(frame.results.val+1)+frame.results.val+1 = compiler.height.val
      omega
    by_cases elided : frame.results = 0#u32 ∨ source = frame.height
    · apply WP.spec_mono (branch_if_elided_forward_available ops bound available compiler state (capacity.mono (by decide))
        frame index depth source condition lookup position loopEntry elided sourcePosition conditionAt fixupsCapacity fixupsReserve)
      intro out post
      exact ⟨post.1,post.2.weaken (by intro counter; cases counter <;> simp)⟩
    · exact branch_if_transfer_forward_available ops law bound available compiler state capacity frame index depth source condition
        lookup position loopEntry (by intro zero; exact elided (.inl zero))
        (by intro same; exact elided (.inr same)) sourcePosition conditionAt fixupsCapacity fixupsReserve

/-- The actual br_if callback also accepts unreachable paths, which only
observe the validator stack and retain the compilation budget. -/
theorem compiler_on_br_if_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 3)
    (frame : runtime.compiler.Frame) (index : Usize) (depth condition : U32) (resultType : Itasca.signature.ResultType)
    (lookup : compiler.reachable = true → compiler.frames.val[index.val]? = some frame)
    (position : compiler.reachable = true → index.val + depth.val + 1 = compiler.frames.val.length)
    (widthFits : compiler.reachable = true →
      (match frame.kind with | .Loop => frame.params | _ => frame.results).val + 1 ≤ compiler.height.val)
    (conditionAt : compiler.reachable = true → compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (fixupsCapacity : frame.fixups.length < Usize.max)
    (fixupsReserve : frame.fixups.length + 1 ≤ bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops compiler state depth resultType ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 3 else 0) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
  by_cases live : compiler.reachable = true
  · rw [if_pos live]
    obtain ⟨⟨status,branched⟩,actual,accepted,effect⟩ := WP.spec_imp_exists
      (compiler_conditional_branch_available ops law bound available compiler state capacity frame index depth condition
        (lookup live) (position live) (widthFits live) (conditionAt live) fixupsCapacity fixupsReserve)
    dsimp only at accepted effect
    subst status
    rw [actual]
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have stable := compiler_branch_stable_result ops law compiler branched depth 1#u32 true (.Ok ()) actual
    have localsSame := stable.fields.2.2.2.2.2.2.1
    have slotsFit : branched.function.local_slots.val + 2*state.vals.length ≤ U32.max := by
      rw [localsSame]; exact capacity.slots
    apply WP.spec_mono (compiler_observe_available_budget ops bound available branched state capacity.operands slotsFit)
    intro out post
    rw [post.2]
    exact ⟨post.1,effect⟩
  · rw [if_neg live]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state capacity.operands capacity.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Runtime.Compiler

end

end

/-! ## ElseDispatchAvailability -/

section

/-!
Availability of else callbacks in live, dormant and unentered cases. The final dispatch theorem chooses the actual case without assuming callback success.
-/

/-! ## Else Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Live else entry accepts a bounded skip-fixup append, one emitted jump,
and its owned guard patch. Only the instruction counter changes. -/
theorem compiler_else_live_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (guard : Usize) (condition target : U32)
    (frames : compiler.frames.val = prior ++ [frame])
    (reachable : compiler.reachable = true) (guardPc : frame.if_pc = some guard)
    (guardCode : compiler.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX))
    (position : target.val = compiler.function.code.val.length + 1)
    (fixupsCapacity : frame.fixups.length < Usize.max)
    (fixupsReserve : frame.fixups.length + 1 ≤ bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  have nonempty : compiler.frames.val.isEmpty = false := by simp [frames]
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
  simp only [alloc.vec.Vec.is_empty, bind_ok, nonempty, Bool.false_eq_true, ite_false]
  step as ⟨index, indexEq⟩
  have atLast : index.val = prior.length := by simp [frames, alloc.vec.Vec.len] at indexEq; omega
  step as ⟨found, back, foundEq, backEq⟩
  have same : found = frame := by simpa [atLast, frames] using foundEq
  rw [same]
  simp only [core.option.Option.take, guardPc, reachable, ite_true, Bool.or_true]
  step with budget_push_available ops bound available compiler.budget frame.fixups (alloc.vec.Vec.len compiler.function.code)
    fixupsCapacity fixupsReserve as ⟨status,budget,fixups,accepted,same,appended⟩
  subst status budget
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  let updated := {compiler with
    frames := back {frame with kind := .Else,if_pc := none,end_reachable := true,fixups}
    reachable := frame.entry_reachable}
  have updatedDemand : CallbackDemand updated state bound :=
    ⟨demand.pc,demand.codeCapacity,demand.sourceCapacity,demand.codeReserve,demand.sourceReserve,
      demand.coordinate,demand.instruction,demand.operands,demand.slots⟩
  step with compiler_emit_available_frame ops bound available updated (.Jump core.num.U32.MAX)
    updatedDemand.pc updatedDemand.codeCapacity updatedDemand.sourceCapacity updatedDemand.codeReserve
    updatedDemand.sourceReserve updatedDemand.coordinate updatedDemand.instruction
    as ⟨status,emitted,accepted,used,code,offsets,emittedEq,usedEq,codeAppend,_⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  rw [compiler_pc_eq ops emitted target (by simpa [emittedEq,codeAppend,updated] using position)]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  have guardBound := (List.getElem?_eq_some_iff.mp guardCode).1
  have retained : emitted.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX) := by
    simp only [emittedEq,codeAppend,updated]
    rw [List.getElem?_append_left guardBound]
    exact guardCode
  step with compiler_patch ops emitted guard (.zero condition) core.num.U32.MAX target retained
    as ⟨status,patched,statusEq,patchedEffect⟩
  subst status
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  obtain ⟨newCode,patchedEq,_⟩ := patchedEffect
  have slotsFit : patched.function.local_slots.val + 2*state.vals.length ≤ U32.max := by
    rw [patchedEq,emittedEq]; exact demand.slots
  have budgetEq : patched.budget = {compiler.budget with instructions := used} := by
    rw [patchedEq,emittedEq]
  apply WP.spec_mono (compiler_observe_available_budget ops bound available patched state demand.operands slotsFit)
  intro out post
  rw [post.2,budgetEq]
  exact ⟨post.1,.of_counter .instructions compiler.budget used 1
    (by simp [updated,ChargeCounter.used] at usedEq ⊢; omega)
    (by simp [updated,ChargeCounter.used] at usedEq ⊢; omega)⟩

/-- An else path without fallthrough emits no instruction and retains the complete budget. -/
theorem compiler_else_dead_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (guard : Usize) (condition target : U32)
    (frames : compiler.frames.val = prior ++ [frame])
    (reachable : compiler.reachable = false) (guardPc : frame.if_pc = some guard)
    (guardCode : compiler.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX))
    (position : target.val = compiler.function.code.val.length)
    (request : state.vals.length ≤ bound)
    (slotsFit : compiler.function.local_slots.val + 2*state.vals.length ≤ U32.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ out =>
      out.1 = .Ok () ∧ out.2.budget = compiler.budget ⦄ := by
  have nonempty : compiler.frames.val.isEmpty = false := by simp [frames]
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
  simp only [alloc.vec.Vec.is_empty, bind_ok, nonempty, Bool.false_eq_true, ite_false]
  step as ⟨index, indexEq⟩
  have atLast : index.val = prior.length := by simp [frames, alloc.vec.Vec.len] at indexEq; omega
  step as ⟨found, back, foundEq, backEq⟩
  have same : found = frame := by simpa [atLast, frames] using foundEq
  rw [same]
  simp only [core.option.Option.take, guardPc, reachable, Bool.false_eq_true, ite_false, Bool.or_false]
  let updated := { compiler with frames := back { frame with kind := .Else, if_pc := none }, reachable := frame.entry_reachable }
  rw [compiler_pc_eq ops updated target position]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step with compiler_patch ops updated guard (.zero condition) core.num.U32.MAX target guardCode
    as ⟨status, patched, statusEq, patchedEffect⟩
  subst status
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨newCode, patchedEq, codeSet⟩ := patchedEffect
  have patchedSlots : patched.function.local_slots.val + 2*state.vals.length ≤ U32.max := by
    rw [patchedEq]; exact slotsFit
  have patchedBudget : patched.budget = compiler.budget := by rw [patchedEq]
  simpa only [patchedBudget] using compiler_observe_available_budget ops bound available patched state request patchedSlots

/-- An else path without fallthrough emits no instruction and retains the complete budget. -/
theorem compiler_else_unentered_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (frames : compiler.frames.val = prior ++ [frame])
    (reachable : compiler.reachable = false) (guardPc : frame.if_pc = none)
    (request : state.vals.length ≤ bound)
    (slotsFit : compiler.function.local_slots.val + 2*state.vals.length ≤ U32.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ out =>
      out.1 = .Ok () ∧ out.2.budget = compiler.budget ⦄ := by
  have nonempty : compiler.frames.val.isEmpty = false := by simp [frames]
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
  simp only [alloc.vec.Vec.is_empty, bind_ok, nonempty, Bool.false_eq_true, ite_false]
  step as ⟨index, indexEq⟩
  have atLast : index.val = prior.length := by simp [frames, alloc.vec.Vec.len] at indexEq; omega
  step as ⟨found, back, foundEq, backEq⟩
  have same : found = frame := by simpa [atLast, frames] using foundEq
  rw [same]
  simp only [core.option.Option.take, guardPc, reachable, Bool.false_eq_true, ite_false, Bool.or_false]
  let updated := {compiler with
    frames := back {frame with kind := .Else,if_pc := none}
    reachable := frame.entry_reachable}
  exact compiler_observe_available_budget ops bound available updated state request slotsFit

end Itasca.Runtime.Compiler

end

/-! ## Else Dispatch Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

private theorem representable_pc (count : Nat) (bounded : count ≤ U32.max) :
    ∃ pc : U32, pc.val = count := by
  have fits : count < 2^UScalarTy.U32.numBits := by scalar_tac
  exact ⟨U32.ofNatCore count fits,U32.ofNatCore_val_eq fits⟩

/-- Every valid else state accepts. Numeric capacity constructs the target
PC; retained guard ownership and entry metadata discharge the live/dead cases.
No successful callback equation is supplied by the caller. -/
theorem compiler_else_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 1) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (frames : compiler.frames.val = prior ++ [frame])
    (liveGuard : compiler.reachable = true → frame.if_pc ≠ none)
    (guardOwned : ∀ guard, frame.if_pc = some guard → ∃ condition,
      compiler.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX))
    (fixupsCapacity : frame.fixups.length < Usize.max)
    (fixupsReserve : frame.fixups.length + 1 ≤ bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨target,position⟩ := representable_pc (compiler.function.code.length+1) capacity.pc
    cases guardPc : frame.if_pc with
    | none => exact False.elim (liveGuard live guardPc)
    | some guard =>
      obtain ⟨condition,guardCode⟩ := guardOwned guard guardPc
      exact compiler_else_live_available ops bound available compiler state (capacity.one (by decide)) bt
        frame prior guard condition target frames live guardPc guardCode position fixupsCapacity fixupsReserve
  · have dead : compiler.reachable = false := Bool.eq_false_iff.mpr live
    cases guardPc : frame.if_pc with
    | none =>
      apply WP.spec_mono (compiler_else_unentered_available ops bound available compiler state bt frame prior frames
        dead guardPc capacity.operands capacity.slots)
      intro out post
      rw [post.2]
      exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩
    | some guard =>
      obtain ⟨condition,guardCode⟩ := guardOwned guard guardPc
      obtain ⟨target,position⟩ := representable_pc compiler.function.code.length (by have room := capacity.pc; omega)
      apply WP.spec_mono (compiler_else_dead_available ops bound available compiler state bt frame prior guard condition
        target frames dead guardPc guardCode position capacity.operands capacity.slots)
      intro out post
      rw [post.2]
      exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Runtime.Compiler

end

end

/-! ## SimdOpAvailability -/

section

/-!
Availability of SIMD opcode construction and compiler callbacks. Immediate-meaning certificates discharge constructor obligations before constant/nonconstant replay.
-/

/-! ## Simd Constructor Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

/-- Independent source opcode meaning excludes every reserved constructor
case. This covers all nonconstant SIMD families, without assuming construction
or successful compilation. -/
theorem SimdImmediateMeaning.constructor_available {C opcode immediate input source output}
    (meaning : SimdImmediateMeaning C opcode immediate input source output)
    (bounded : opcode.val < 256) (dst operand entry : U32) :
    ∃ instruction, runtime.bytecode.Instr.make_simd opcode dst operand entry = .ok (some instruction) := by
  rcases opcode with ⟨⟨number,numberBound⟩⟩
  change number < 256 at bounded
  interval_cases number <;> first
    | exact ⟨_,rfl⟩
    | (cases meaning with
      | pure _ _ _ decoded => change none = some _ at decoded; contradiction
      | lane _ _ _ decoded _ _ => change none = some _ at decoded; contradiction
      | memory _ _ _ decoded _ _ _ _ _ _ => change none = some _ at decoded; contradiction)

end Itasca.Runtime.Compiler

end

/-! ## Simd Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Nonconstant SIMD lowering accepts from independent source meaning and
stack lengths. Temporary arithmetic and the immediate-table request are
bounded explicitly; source meaning discharges constructor coverage. -/
theorem compiler_simd_nonconstant_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (C : context)
    (front input output : List valtype) (source : instr)
    (opcode : U16) (sub a : U32) (bits : U128)
    (number : opcode.val = 512 + sub.val) (bounded : sub.val < 256)
    (nonconstant : sub.val ≠ 12)
    (meaning : SimdImmediateMeaning C sub (simdImmediate sub a bits) input source output)
    (layout : CompilerLayout compiler (front ++ input))
    (postLength : state.vals.val.length = (front ++ output).length)
    (operandCapacity : compiler.before.length < Usize.max)
    (tableIndex : compiler.function.simd.length ≤ U32.max)
    (tableCapacity : compiler.function.simd.length < Usize.max)
    (tableReserve : compiler.function.simd.length + 1 ≤ bound) :
    runtime.compiler.simd.FunctionCompiler.simd_op ops compiler state opcode a bits
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  have notConstant : opcode ≠ 524#u16 := by
    intro same
    have numeric := congrArg UScalar.val same
    change opcode.val = 524 at numeric
    omega
  rw [compiler_simd_nonconstant_eq ops compiler state opcode a bits notConstant (by omega) (by omega)]
  obtain ⟨reduced,reducedEq,subEq⟩ := simd_opcode_reduction opcode sub number
  unfold simdLowering
  simp only [reducedEq,lift,bind_ok,←subEq,simd_stores_eq,simd_outputs_eq]
  have beforeLength := layout.operands_length
  have outputs := meaning.output_count
  have positive := meaning.input_positive
  simp only [List.length_append] at beforeLength postLength
  have addSpec := Usize.checked_add_bv_spec (alloc.vec.Vec.len compiler.before)
    (if simdStores sub then 0#usize else 1#usize)
  cases added : Usize.checked_add (alloc.vec.Vec.len compiler.before)
      (if simdStores sub then 0#usize else 1#usize) with
  | none =>
    simp only [added] at addSpec
    split at addSpec <;> scalar_tac
  | some total =>
    simp only [added] at addSpec
    have totalCount : total.val = compiler.before.length + (if simdStores sub then 0 else 1) := by
      split at addSpec <;> simp_all only [↓reduceIte] <;> scalar_tac
    simp only [added,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have subSpec := Usize.checked_sub_bv_spec total (alloc.vec.Vec.len state.vals)
    cases subtracted : Usize.checked_sub total (alloc.vec.Vec.len state.vals) with
    | none => simp only [subtracted] at subSpec; scalar_tac
    | some consumed =>
      simp only [subtracted] at subSpec
      have consumedCount : consumed.val = input.length := by scalar_tac
      simp only [subtracted,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      obtain ⟨status,read,operand,accepted,_⟩ := WP.spec_imp_exists
        (compiler_operand ops compiler _ layout consumed (by omega) (by simp [consumedCount]))
      subst status
      rw [read]
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      step with bounded_index_available (alloc.vec.Vec.len compiler.function.simd) tableIndex
        as ⟨status,index,accepted,_⟩
      rw [accepted]
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,simd_lane_eq]
      step with budget_push_available ops bound available compiler.budget compiler.function.simd
        ({offset := a,lane := simdLane sub a bits,bits} : runtime.bytecode.SimdImmediate) tableCapacity tableReserve
        as ⟨status,budget,values,accepted,same,_⟩
      rw [accepted,same]
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      obtain ⟨instruction,constructed⟩ := meaning.constructor_available bounded operand operand index
      rw [constructed]
      simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      let allocated := {compiler with function := {compiler.function with simd := values}}
      have afterDemand : CallbackDemand allocated state bound :=
        ⟨demand.pc,demand.codeCapacity,demand.sourceCapacity,demand.codeReserve,
          demand.sourceReserve,demand.coordinate,demand.instruction,demand.operands,demand.slots⟩
      exact finish_op_available_effect ops bound available allocated state afterDemand instruction

end Itasca.Runtime.Compiler

end

/-! ## Simd Op Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Actual ordinary dispatch for every meaningful nonconstant SIMD opcode
accepts on live and dead paths. The immediate ledger bounds its own reserve. -/
theorem compiler_simd_nonconstant_op_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (C : context)
    (front input output : List valtype) (source : instr)
    (opcode : U16) (sub a b : U32) (bits : U128)
    (number : opcode.val = 512+sub.val) (bounded : sub.val < 256) (nonconstant : sub.val ≠ 12)
    (meaning : SimdImmediateMeaning C sub (simdImmediate sub a bits) input source output)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ input))
    (postLength : compiler.reachable = true → state.vals.val.length = (front ++ output).length)
    (operandCapacity : compiler.before.length < Usize.max)
    (tableBound : compiler.function.simd.length ≤ compiler.function.code.length) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state opcode a b bits ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨out,actual,post⟩ := WP.spec_imp_exists
      (compiler_simd_nonconstant_available ops bound available compiler state demand C front input output source
        opcode sub a bits number bounded nonconstant meaning (layout live) (postLength live) operandCapacity
        (tableBound.trans demand.pc) (tableBound.trans_lt demand.codeCapacity)
        ((Nat.add_le_add_right tableBound 1).trans demand.codeReserve))
    exact WP.exists_imp_spec ⟨out,
      (lower_simd_dispatch ops compiler state opcode a b bits live (by omega) (by omega)).trans actual,post⟩
  · apply WP.spec_mono (compiler_dead_op_available ops bound available compiler state opcode a b bits live
      demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

/-- The actual vector-constant dispatch accepts its bounded pool append and
instruction charge, including dead code where no pool entry is allocated. -/
theorem compiler_simd_constant_op_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (bits : U128)
    (poolBound : compiler.function.v128_pool.length ≤ compiler.function.code.length) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 524#u16 0#u32 0#u32 bits ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨out,actual,post⟩ := WP.spec_imp_exists
      (compiler_vector_literal_available_budget ops bound available compiler state demand poolBound bits)
    obtain ⟨used,budgetEq,usedEq⟩ := post.2
    have effect : CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) := by
      rw [budgetEq]
      exact .of_counter .instructions compiler.budget used 1
        (by simp [ChargeCounter.used]; omega) (by simp [ChargeCounter.used]; omega)
    exact WP.exists_imp_spec ⟨out,
      (lower_simd_dispatch ops compiler state 524#u16 0#u32 0#u32 bits live (by decide) (by decide)).trans actual,
      post.1,effect⟩
  · apply WP.spec_mono (compiler_dead_op_available ops bound available compiler state 524#u16 0#u32 0#u32 bits live
      demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Runtime.Compiler

end

end

/-! ## SimdCallbacksAvailability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The vector-constant hook preserves the actual packed source bits in
its pool and charges at most one instruction. -/
theorem compiler_on_simd_const_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (lo hi : U64)
    (poolBound : compiler.function.v128_pool.length ≤ compiler.function.code.length) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_const compiler state lo hi ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [compiler_simd_constant_callback ops compiler state lo hi]
  exact compiler_simd_constant_op_available ops bound available compiler state demand (initializerBits lo hi) poolBound

end Itasca.Runtime.Compiler

end
