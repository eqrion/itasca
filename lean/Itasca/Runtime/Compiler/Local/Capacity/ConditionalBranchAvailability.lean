import Itasca.Runtime.Compiler.Local.Capacity.CallbackCapacity
import Itasca.Runtime.Compiler.Local.Lowering.Control.LoweringBranchIf
import Itasca.Runtime.Compiler.Local.Capacity.TransferAvailability
import Itasca.Runtime.Compiler.Local.Lowering.Control.LoweringConditionalTransfer
import Itasca.Runtime.Compiler.Local.Capacity.ObserveBudgetAvailability
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerBranchMetadata

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
