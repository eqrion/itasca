import Exec.Code.Local.Capacity.FunctionStartAvailability
import Exec.Code.Local.Capacity.BodyResourceRoom
import Exec.Code.Local.Relations.Common.FunctionEntry

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Conservative function demand measured solely in source body bytes,
expanded local declarations, and independently validated operand peak. -/
structure PreparedFunctionDemand {A : Type} (budget : runtime.compiler.Budget A)
    (ctx : code.Context) (length peak bound : Nat) : Prop where
  size : length ≤ limits.MAX_FUNCTION_BYTES.val
  instructions : budget.instructions.val+3*length ≤ budget.limits.max_instructions.val
  branches : budget.branches.val+length ≤ budget.limits.max_branch_table_entries.val
  controls : budget.controls.val+1+length ≤ budget.limits.max_controls.val
  locals : budget.locals.val+ctx.locals.val.length ≤ budget.limits.max_locals.val
  temporary : 3*length+3 ≤ bound
  localReserve : ctx.locals.val.length ≤ bound
  operands : peak ≤ bound
  slots : 2*ctx.locals.val.length+2*peak ≤ U32.max

/-- Fresh compiler construction turns source-only demand into every reserve
and arithmetic premise of the actual function-start callback. -/
theorem PreparedFunctionDemand.start {A : Type}
    {budget : runtime.compiler.Budget A} {ctx length peak bound}
    (demand : PreparedFunctionDemand budget ctx length peak bound)
    (ops : runtime.platform.Alloc A) (signatures : Slice runtime.compiler.Signature)
    (functionSlots : Slice U32) (batchStart : Usize) (initial : runtime.compiler.FunctionCompiler A)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial) :
    FunctionStartDemand initial ctx bound := by
  simp only [runtime.compiler.FunctionCompiler.new,Result.ok.injEq] at created
  subst initial
  have wordBound : U32.max ≤ Usize.max := by scalar_tac
  have localBound : ctx.locals.val.length ≤ Usize.max := by have slots := demand.slots; omega
  have one : 1 ≤ bound := by have temporary := demand.temporary; omega
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact demand.locals
  · simpa [alloc.vec.Vec.new] using localBound
  · simpa [alloc.vec.Vec.new] using demand.localReserve
  · simpa [alloc.vec.Vec.new] using localBound
  · simpa [alloc.vec.Vec.new] using demand.localReserve
  · have slots := demand.slots
    simp only [show (0#u32).val = 0 from rfl,Nat.zero_add]
    omega
  · change budget.controls.val < budget.limits.max_controls.val
    have controls := demand.controls
    omega
  · simp [alloc.vec.Vec.new]; scalar_tac
  · simpa [alloc.vec.Vec.new] using one
  · simp [alloc.vec.Vec.new]; scalar_tac
  · simpa [alloc.vec.Vec.new] using one

/-- The actual start budget and local layout transfer the independent demand
into the complete body acceptance bound. -/
theorem PreparedFunctionDemand.body {A : Type}
    {budget : runtime.compiler.Budget A} {ctx length peak bound}
    (demand : PreparedFunctionDemand budget ctx length peak bound)
    (started : runtime.compiler.FunctionCompiler A) (usedLocals usedControls : Usize)
    (budgetFrame : started.budget = {budget with locals := usedLocals,controls := usedControls})
    (localsUsed : usedLocals.val = budget.locals.val+ctx.locals.val.length)
    (controlsUsed : usedControls.val = budget.controls.val+1)
    (layout : LocalLayout started) (localsMatch : started.function.locals = ctx.locals)
    (coordinate : started.function.body_start.val+length ≤ Usize.max) :
    BodyResourceRoom started length peak bound := by
  refine ⟨demand.size,?_,demand.temporary,demand.operands,?_,coordinate⟩
  · intro counter
    cases counter <;> simp only [ChargeCounter.used,ChargeCounter.limit,bodyResourceRate,budgetFrame,
      Nat.zero_mul,Nat.one_mul,localsUsed,controlsUsed]
    · exact demand.instructions
    · exact demand.branches
    · exact demand.controls
    · simpa only [Nat.add_zero] using demand.locals
  · have slotBound := slots_le_twice_length (compilerLocals started)
    have localLength : (compilerLocals started).length = ctx.locals.val.length := by
      simp [compilerLocals,localsMatch]
    rw [localLength] at slotBound
    rw [layout.slots]
    have room := demand.slots
    omega

end Exec.Code
