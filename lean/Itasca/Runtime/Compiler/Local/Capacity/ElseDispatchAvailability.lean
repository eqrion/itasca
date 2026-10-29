import Itasca.Runtime.Compiler.Local.Capacity.FinishBudgetAvailability
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterElse
import Itasca.Runtime.Compiler.Local.Capacity.CallbackCapacity

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
