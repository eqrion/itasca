import Exec.Code.Local.Initializer.InitializerExpression
import Exec.Code.Local.Relations.Common.WellFormedAcceptance
import Exec.Code.Local.Capacity.BudgetAvailability

/-! Acceptance of synthetic initializers from source shape and available
resources, rather than an assumed successful publication check. -/
namespace Exec.Code
open Aeneas Aeneas.Std

private theorem slots_fit_zero (function : runtime.bytecode.CompiledFunction) (count : U32)
    (bounded : count.val ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.slots_fit function 0#u32 count = .ok true := by
  have below : 0#u32 ≤ function.slot_count := by scalar_tac
  simp only [runtime.bytecode.CompiledFunction.slots_fit,if_pos below]
  have check : runtime.bytecode.CompiledFunction.slots_fit function 0#u32 count
      ⦃ result => result = true ⦄ := by
    unfold runtime.bytecode.CompiledFunction.slots_fit
    simp only [if_pos below]
    step as ⟨left,equal⟩
    have fits : count ≤ left := by scalar_tac
    simp [fits]
  obtain ⟨result,actual,rfl⟩ := WP.spec_imp_exists check
  exact actual

/-- The only extra width condition is independently visible in the source:
a vector literal requires a vector result slot. Other constant-expression
forms fit the width selected from their result type. -/
theorem initial_instruction_accepts (function : runtime.bytecode.CompiledFunction)
    (expr : Itasca.types.ConstExpr) (ty : Itasca.types.ValueType) (instruction : runtime.bytecode.Instr)
    (lowered : InitialInstruction function expr ty instruction)
    (capacity : function.slot_count = initializerWidth ty)
    (vector : ∀ lo hi, expr = .V128 lo hi → ty = .V128) :
    runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  have scalar : runtime.bytecode.CompiledFunction.slots_fit function 0#u32 1#u32 = .ok true := by
    apply slots_fit_zero
    rw [capacity]
    cases ty <;> decide
  have wide (same : ty = .V128) :
      runtime.bytecode.CompiledFunction.slots_fit function 0#u32 2#u32 = .ok true := by
    apply slots_fit_zero
    simp [capacity,same,initializerWidth]
  cases lowered <;>
    simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.Instr.scalar,
      runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok]
  all_goals first | exact scalar | exact wide rfl | skip
  rename_i lo hi pool embedded
  rw [wide (vector lo hi rfl),bind_ok]
  have inside := (List.getElem?_eq_some_iff.mp embedded).1
  have poolBound : UScalar.cast .Usize pool < alloc.vec.Vec.len function.v128_pool := by scalar_tac
  simpa [lift] using inside

/-- Exact initializer code and source metadata imply the actual publication
checker accepts. Component checker success is derived here, not assumed. -/
theorem initializer_well_formed (function : runtime.bytecode.CompiledFunction)
    (expr : Itasca.types.ConstExpr) (ty : Itasca.types.ValueType)
    (shape : InitializerCode function expr ty)
    (start : function.body_start = 0#usize) (finish : function.body_end = 0#usize)
    (offsets : function.source_offsets.val = []) (jumps : function.jump_tables.val = [])
    (controls : function.controls.val = [])
    (vector : ∀ lo hi, expr = .V128 lo hi → ty = .V128) :
    runtime.bytecode.CompiledFunction.well_formed function ⦃ result => result = true ⦄ := by
  obtain ⟨instruction,lowered,code⟩ := shape.code
  have length : function.code.length = 2 := by simp [alloc.vec.Vec.length,code]
  apply well_formed_synthetic_accepts function start finish (by omega) offsets
    (by rw [shape.localSlots,shape.capacity]; cases ty <;> decide)
    (by rw [shape.paramSlots,shape.localSlots]) 0#u32 (initializerWidth ty)
  · simp [length,code]
  · intro j bounded
    rw [length] at bounded
    have first := initial_instruction_accepts function expr ty instruction lowered shape.capacity vector
    have returned : runtime.bytecode.CompiledFunction.instruction_valid function
        (.Return 0#u32 (initializerWidth ty)) = .ok true := by
      simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.Instr.scalar,
        runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok]
      exact slots_fit_zero function (initializerWidth ty) (by rw [shape.capacity])
    interval_cases j <;> simpa [code] using (by assumption)
  · simp [jumps]
  · simp [controls]

/-- One available instruction emission consumes one unit of instruction budget
and appends its instruction. Bounds are on actual reserve demand. -/
theorem initializer_emit_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (code : alloc.vec.Vec runtime.bytecode.Instr)
    (instruction : runtime.bytecode.Instr)
    (room : budget.instructions.val < budget.limits.max_instructions.val)
    (fits : code.length < Usize.max) (request : code.length + 1 ≤ bound) :
    runtime.compiler.initialize.emit ops budget code instruction ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.instructions.val = budget.instructions.val + 1 ∧
      out.2.1.limits = budget.limits ∧ out.2.2.val = code.val ++ [instruction] ⦄ := by
  unfold runtime.compiler.initialize.emit
  step with charge_instruction_available ops budget room as ⟨status,charged,success,used,limits,error⟩
  rw [success]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  apply WP.spec_mono (budget_push_available ops bound available charged code instruction fits request)
  rintro ⟨status,after,values⟩ ⟨rfl,rfl,appended⟩
  exact ⟨rfl,used,limits,appended⟩

end Exec.Code
