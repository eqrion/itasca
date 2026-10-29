import Itasca.Runtime.Compiler.Local.Initializer.InitializerAcceptance
import Itasca.Runtime.Compiler.Local.Relations.Segments.SegmentData

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Source-typed i32 offsets compile with one instruction and no pool reserve.
The exact field effect is available before any publication checker runs. -/
theorem initializer_offset_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction)
    (env : Itasca.module.Env) (expr : Itasca.types.ConstExpr)
    (typed : Itasca.ModuleConstants.Valid env expr .I32)
    (room : budget.instructions.val < budget.limits.max_instructions.val)
    (capacity : function.code.length < Usize.max) (request : function.code.length + 1 ≤ bound) :
    runtime.compiler.initialize.constant ops budget function expr .I32 0#u32 ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.instructions.val = budget.instructions.val + 1 ∧
      out.2.1.limits = budget.limits ∧ out.2.2 = {function with code := out.2.2.code} ∧
      ∃ instruction, out.2.2.code.val = function.code.val ++ [instruction] ∧
        ConstantInstruction out.2.2 0#u32 expr .I32 instruction ⦄ := by
  rcases valid_offset_shape typed with ⟨bits,rfl⟩ | ⟨index,rfl⟩
  · unfold runtime.compiler.initialize.constant
    step as ⟨word,wordEq⟩
    subst word
    step with initializer_emit_available ops bound available budget function.code _ room capacity request
      as ⟨status,charged,instructions,accepted,used,limits,appended⟩
    exact ⟨accepted,used,limits,_,appended,.i32 bits .I32⟩
  · unfold runtime.compiler.initialize.constant
    simp only [bind_ok]
    step with initializer_emit_available ops bound available budget function.code _ room capacity request
      as ⟨status,charged,instructions,accepted,used,limits,appended⟩
    exact ⟨accepted,used,limits,_,appended,.global .I32 index (by intro h; cases h)⟩

end Itasca.Runtime.Code
