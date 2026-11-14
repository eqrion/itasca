import Itasca.Runtime.Compiler.Local.Capacity.UnreachableAvailability
import Itasca.Runtime.Compiler.Local.Lowering.Control.LoweringTrap
import Itasca.Runtime.Compiler.Local.Capacity.CallAvailability
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdDispatch
import Mathlib.Tactic.IntervalCases
import Itasca.Runtime.Compiler.Local.Capacity.GlobalAvailability
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdBitsCallbacks
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Control.BranchCallbacks

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
  have width : branchWidth frame = frame.params := by
    simp only [branchWidth, kind]
  have count : branchInstructionCount true frame source = 1 := by
    simp only [branchInstructionCount, width, if_pos elided]
  have demand : BranchDemand compiler frame bound 1 := {
    pc := capacity.pc, code := capacity.codeCapacity, sources := capacity.sourceCapacity
    codeReserve := capacity.codeReserve, sourceReserve := capacity.sourceReserve
    coordinate := capacity.coordinate, instructions := capacity.instructions
    fixups := fun different => False.elim (different kind)
    fixupsReserve := fun different => False.elim (different kind) }
  have ready : true = true → ∃ condition,
      runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok condition) := by
    intro _
    obtain ⟨answer, called, same⟩ := WP.spec_imp_exists (compiler_condition ops compiler condition conditionAt)
    exact ⟨condition, same ▸ called⟩
  apply WP.spec_mono (runtime.compiler.control.FunctionCompiler.branch.available ops bound available
    compiler depth 1#u32 true ⟨index, frame, lookup, position⟩ source
    (by simpa only [width, UScalar.ofNatCore_val_eq] using sourcePosition) ready (by simpa only [count] using demand))
  intro output effect
  have budget := effect.2.compilation
  exact ⟨effect.1, by simpa only [count] using budget⟩

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
  have width : branchWidth frame = frame.results := by
    cases kind : frame.kind <;> simp only [branchWidth, kind]
    exact False.elim (forward kind)
  have count : branchInstructionCount true frame source = 1 := by
    simp only [branchInstructionCount, width, if_pos elided]
  have demand : BranchDemand compiler frame bound 1 := {
    pc := capacity.pc, code := capacity.codeCapacity, sources := capacity.sourceCapacity
    codeReserve := capacity.codeReserve, sourceReserve := capacity.sourceReserve
    coordinate := capacity.coordinate, instructions := capacity.instructions
    fixups := fun _ => fixupsCapacity, fixupsReserve := fun _ => fixupsReserve }
  have ready : true = true → ∃ condition,
      runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok condition) := by
    intro _
    obtain ⟨answer, called, same⟩ := WP.spec_imp_exists (compiler_condition ops compiler condition conditionAt)
    exact ⟨condition, same ▸ called⟩
  apply WP.spec_mono (runtime.compiler.control.FunctionCompiler.branch.available ops bound available
    compiler depth 1#u32 true ⟨index, frame, lookup, position⟩ source
    (by simpa only [width, UScalar.ofNatCore_val_eq] using sourcePosition) ready (by simpa only [count] using demand))
  intro output effect
  have budget := effect.2.compilation
  exact ⟨effect.1, by simpa only [count] using budget⟩

end Itasca.Runtime.Compiler

end

/-! ## Conditional Transfer Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096


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
  have width : branchWidth frame = frame.params := by
    simp only [branchWidth, kindEq]
  have no : ¬ (branchWidth frame = 0#u32 ∨ source = frame.height) := by
    rw [width]
    exact fun choice => choice.elim nonempty different
  have count : branchInstructionCount true frame source = 3 := by
    simp only [branchInstructionCount, if_neg no, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false]
  have demand : BranchDemand compiler frame bound 3 := {
    pc := capacity.pc, code := capacity.codeCapacity, sources := capacity.sourceCapacity
    codeReserve := capacity.codeReserve, sourceReserve := capacity.sourceReserve
    coordinate := capacity.coordinate, instructions := capacity.instructions
    fixups := fun different => False.elim (different kindEq)
    fixupsReserve := fun different => False.elim (different kindEq) }
  have ready : true = true → ∃ condition,
      runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok condition) := by
    intro _
    obtain ⟨answer, called, same⟩ := WP.spec_imp_exists (compiler_condition ops compiler condition conditionAt)
    exact ⟨condition, same ▸ called⟩
  apply WP.spec_mono (runtime.compiler.control.FunctionCompiler.branch.available ops bound available
    compiler depth 1#u32 true ⟨index, frame, lookup, position⟩ source
    (by simpa only [width, UScalar.ofNatCore_val_eq] using sourcePosition) ready (by simpa only [count] using demand))
  intro output effect
  have budget := effect.2.compilation
  exact ⟨effect.1, by simpa only [count] using budget⟩

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
  have width : branchWidth frame = frame.results := by
    cases kind : frame.kind <;> simp only [branchWidth, kind]
    exact False.elim (forward kind)
  have no : ¬ (branchWidth frame = 0#u32 ∨ source = frame.height) := by
    rw [width]
    exact fun choice => choice.elim nonempty different
  have count : branchInstructionCount true frame source = 3 := by
    simp only [branchInstructionCount, if_neg no, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false]
  have demand : BranchDemand compiler frame bound 3 := {
    pc := capacity.pc, code := capacity.codeCapacity, sources := capacity.sourceCapacity
    codeReserve := capacity.codeReserve, sourceReserve := capacity.sourceReserve
    coordinate := capacity.coordinate, instructions := capacity.instructions
    fixups := fun _ => fixupsCapacity, fixupsReserve := fun _ => fixupsReserve }
  have ready : true = true → ∃ condition,
      runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok condition) := by
    intro _
    obtain ⟨answer, called, same⟩ := WP.spec_imp_exists (compiler_condition ops compiler condition conditionAt)
    exact ⟨condition, same ▸ called⟩
  apply WP.spec_mono (runtime.compiler.control.FunctionCompiler.branch.available ops bound available
    compiler depth 1#u32 true ⟨index, frame, lookup, position⟩ source
    (by simpa only [width, UScalar.ofNatCore_val_eq] using sourcePosition) ready (by simpa only [count] using demand))
  intro output effect
  have budget := effect.2.compilation
  exact ⟨effect.1, by simpa only [count] using budget⟩

end Itasca.Runtime.Compiler

end

/-! ## Conditional Branch Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

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
  have ready : compiler.reachable = true → BranchCallbackReady ops compiler depth true bound := by
    intro live
    let selected : BranchSelection compiler depth := ⟨index, frame, lookup live, position live⟩
    have width : (branchWidth frame).val + 1 ≤ compiler.height.val := by
      change (match frame.kind with | .Loop => frame.params | _ => frame.results).val + 1 ≤ compiler.height.val
      exact widthFits live
    let source : U32 := UScalar.ofNatCore (compiler.height.val - ((branchWidth frame).val + 1)) (by scalar_tac)
    have sourcePosition : source.val + (branchWidth frame).val + 1 = compiler.height.val := by
      change compiler.height.val - ((branchWidth frame).val + 1) + (branchWidth frame).val + 1 = compiler.height.val
      omega
    obtain ⟨answer, called, same⟩ := WP.spec_imp_exists
      (compiler_condition ops compiler condition (conditionAt live))
    have operandRead : runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok condition) :=
      same ▸ called
    have countBound : branchInstructionCount true frame source ≤ 3 := by
      unfold branchInstructionCount
      split <;> simp
    have base : BranchCapacity compiler bound (branchInstructionCount true frame source) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, capacity.coordinate, ?_⟩
      · have h := capacity.pc; omega
      · have h := capacity.codeCapacity; omega
      · have h := capacity.sourceCapacity; omega
      · have h := capacity.codeReserve; omega
      · have h := capacity.sourceReserve; omega
      · have h := capacity.instructions; omega
    have demand : BranchDemand compiler frame bound (branchInstructionCount true frame source) := {
      toBranchCapacity := base
      fixups := fun _ => fixupsCapacity
      fixupsReserve := fun _ => fixupsReserve }
    refine ⟨selected, source, ?_, ?_, demand⟩
    · simpa [branchCallbackSkip] using sourcePosition
    · intro _
      exact ⟨condition, operandRead⟩
  apply WP.spec_mono (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if.available
    ops bound available compiler state depth resultType ready capacity.operands capacity.slots)
  intro out post
  rcases out with ⟨status, after⟩
  rcases post with ⟨statusEq, callbackBudget⟩
  subst status
  obtain ⟨used, budgetEq, lower, upper⟩ := callbackBudget.bounds
  refine ⟨rfl, ?_⟩
  rw [budgetEq]
  exact CompilationBudgetEffect.of_counter .instructions compiler.budget used 3 lower upper

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
  have guardSites : ∀ guard, frame.if_pc = some guard →
      ∃ kind old, compiler.function.code.val[guard.val]? = some (BranchKind.instruction kind old) := by
    intro queried h
    have same : queried = guard := Option.some.inj (h.symm.trans guardPc)
    subst queried
    exact ⟨.zero condition, core.num.U32.MAX, by simpa [BranchKind.instruction] using guardCode⟩
  have targetFits : target.val ≤ U32.max := by scalar_tac
  have guardBound : frame.if_pc ≠ none →
      compiler.function.code.length + (if compiler.reachable then 1 else 0) ≤ U32.max := by
    intro _
    rw [reachable]
    simp only [if_true]
    rw [← position]
    omega
  apply WP.spec_mono (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.available
    ops bound available compiler state bt
    ⟨frame, prior, frames, guardSites, guardBound, demand.operands, demand.slots,
      (by intro live; simp [live, fixupsCapacity, fixupsReserve, demand.pc, demand.codeCapacity,
        demand.sourceCapacity, demand.codeReserve, demand.sourceReserve, demand.coordinate, demand.instruction])⟩)
  intro out post
  rcases out with ⟨status, after⟩
  rcases post with ⟨statusOk, used, budgetEq, usedEq⟩
  subst status
  refine ⟨rfl, ?_⟩
  rw [budgetEq]
  exact CompilationBudgetEffect.of_counter .instructions compiler.budget used 1
    (by simp [ChargeCounter.used, reachable] at usedEq ⊢; omega)
    (by simp [ChargeCounter.used, reachable] at usedEq ⊢; omega)

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
  have guardSites : ∀ queried, frame.if_pc = some queried →
      ∃ kind old, compiler.function.code.val[queried.val]? = some (BranchKind.instruction kind old) := by
    intro queried h
    have same : queried = guard := Option.some.inj (h.symm.trans guardPc)
    subst queried
    exact ⟨.zero condition, core.num.U32.MAX, by simpa [BranchKind.instruction] using guardCode⟩
  have guardBound : frame.if_pc ≠ none →
      compiler.function.code.length + (if compiler.reachable then 1 else 0) ≤ U32.max := by
    intro _
    rw [reachable]
    scalar_tac
  apply WP.spec_mono (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.available
    ops bound available compiler state bt
    ⟨frame, prior, frames, guardSites, guardBound, request, slotsFit,
      (by intro live; simp [reachable] at live)⟩)
  intro out post
  rcases out with ⟨status, after⟩
  rcases post with ⟨statusOk, used, budgetEq, usedEq⟩
  subst status
  have usedEqOld : used.val = compiler.budget.instructions.val := by
    simp [reachable] at usedEq
    simpa using usedEq
  have usedSame : used = compiler.budget.instructions := by
    apply UScalar.eq_of_val_eq
    exact usedEqOld
  rw [budgetEq, usedSame]
  exact ⟨rfl, rfl⟩

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
  have guardSites : ∀ queried, frame.if_pc = some queried →
      ∃ kind old, compiler.function.code.val[queried.val]? = some (BranchKind.instruction kind old) := by
    intro queried h
    simp [guardPc] at h
  have guardBound : frame.if_pc ≠ none →
      compiler.function.code.length + (if compiler.reachable then 1 else 0) ≤ U32.max := by
    intro h
    simp [guardPc] at h
  apply WP.spec_mono (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.available
    ops bound available compiler state bt
    ⟨frame, prior, frames, guardSites, guardBound, request, slotsFit,
      (by intro live; simp [reachable] at live)⟩)
  intro out post
  rcases out with ⟨status, after⟩
  rcases post with ⟨statusOk, used, budgetEq, usedEq⟩
  subst status
  have usedEqOld : used.val = compiler.budget.instructions.val := by
    simp [reachable] at usedEq
    simpa using usedEq
  have usedSame : used = compiler.budget.instructions := by
    apply UScalar.eq_of_val_eq
    exact usedEqOld
  rw [budgetEq, usedSame]
  exact ⟨rfl, rfl⟩

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

/-- Independent source opcode meaning excludes every reserved constructor
case. This covers all nonconstant SIMD families, without assuming construction
or successful compilation. -/
private theorem simd_constructor_available_low {C opcode immediate input source output}
    (meaning : SimdImmediateMeaning C opcode immediate input source output)
    (bounded : opcode.val < 128) (dst operand entry : U32) :
    ∃ instruction, runtime.bytecode.Instr.make_simd opcode dst operand entry = .ok (some instruction) := by
  rcases opcode with ⟨⟨number,numberBound⟩⟩
  change number < 128 at bounded
  interval_cases number <;> first
    | exact ⟨_,rfl⟩
    | (cases meaning with
      | pure _ _ _ decoded => change none = some _ at decoded; contradiction
      | lane _ _ _ decoded _ _ => change none = some _ at decoded; contradiction
      | memory _ _ _ decoded _ _ _ _ _ _ => change none = some _ at decoded; contradiction)

private theorem simd_constructor_available_high {C opcode immediate input source output}
    (meaning : SimdImmediateMeaning C opcode immediate input source output)
    (lower : 128 ≤ opcode.val) (bounded : opcode.val < 256) (dst operand entry : U32) :
    ∃ instruction, runtime.bytecode.Instr.make_simd opcode dst operand entry = .ok (some instruction) := by
  rcases opcode with ⟨⟨number,numberBound⟩⟩
  change number < 256 at bounded
  change 128 ≤ number at lower
  interval_cases number <;> first
    | exact ⟨_,rfl⟩
    | (cases meaning with
      | pure _ _ _ decoded => change none = some _ at decoded; contradiction
      | lane _ _ _ decoded _ _ => change none = some _ at decoded; contradiction
      | memory _ _ _ decoded _ _ _ _ _ _ => change none = some _ at decoded; contradiction)

theorem SimdImmediateMeaning.constructor_available {C opcode immediate input source output}
    (meaning : SimdImmediateMeaning C opcode immediate input source output)
    (bounded : opcode.val < 256) (dst operand entry : U32) :
    ∃ instruction, runtime.bytecode.Instr.make_simd opcode dst operand entry = .ok (some instruction) := by
  by_cases low : opcode.val < 128
  · exact simd_constructor_available_low meaning low dst operand entry
  · exact simd_constructor_available_high meaning (by omega) bounded dst operand entry

end Itasca.Runtime.Compiler

end

/-! ## Simd Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

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
  obtain ⟨reduced, reducedEq, subEq⟩ := simd_opcode_reduction opcode sub number
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
    have subSpec := Usize.checked_sub_bv_spec total (alloc.vec.Vec.len state.vals)
    cases subtracted : Usize.checked_sub total (alloc.vec.Vec.len state.vals) with
    | none => simp only [subtracted] at subSpec; scalar_tac
    | some consumed =>
      simp only [subtracted] at subSpec
      have consumedCount : consumed.val = input.length := by scalar_tac
      obtain ⟨status, read, operand, accepted, _⟩ := WP.spec_imp_exists
        (compiler_operand ops compiler _ layout consumed (by omega)
          (by simp only [consumedCount, List.length_append]; omega))
      subst status
      have prepared : SimdOperandInput ops compiler state opcode :=
        ⟨reduced, total, consumed, operand, reducedEq,
          by simpa only [← subEq] using added, subtracted, read,
          by
            intro entry
            simpa only [← subEq] using meaning.constructor_available bounded operand operand entry⟩
      have resources : SimdTailDemand compiler state bound :=
        ⟨demand, tableIndex, tableCapacity, tableReserve⟩
      apply WP.spec_mono (runtime.compiler.simd.FunctionCompiler.simd_op.available ops bound available
        compiler state opcode a bits (.general opcode notConstant (by omega) (by omega) prepared resources))
      intro out post
      obtain ⟨used, same, usedEq⟩ := post.2
      rw [same]
      exact ⟨post.1, .of_counter .instructions compiler.budget used 1
        (by simp only [ChargeCounter.used]; omega)
        (by simp only [ChargeCounter.used]; omega)⟩

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
