import Itasca.Runtime.Compiler.Local.Relations.Instructions.InstructionCheckAcceptance
import Itasca.Runtime.Compiler.Local.Capacity.SimdCapacity

/-!
SIMD checking accepts from the independently selected opcode shape, concrete input/output slot widths, and immediate-table membership.

Main declarations: `simd_instruction_accepts` and `simd_instruction_monotone`. A direct consumer is `Compiler.Local.Checking.OpenInstructionCompiler`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- SIMD checking accepts from the independently selected opcode shape,
concrete input/output slot widths, and immediate-table membership. -/
theorem simd_instruction_accepts (function : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (opcode dst input entry x y z output : U32)
    (projected : runtime.bytecode.Instr.simd instruction = .ok (some (opcode,dst,input,entry)))
    (shape : runtime.bytecode.simd_shape opcode = .ok (some (x,y,z,output)))
    (inputs : input.val+x.val+y.val+z.val ≤ function.slot_count.val)
    (destination : dst.val+output.val ≤ function.slot_count.val)
    (immediate : entry.val < function.simd.length) :
    runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  obtain ⟨scalar,load,store⟩ := simd_view_disjoint instruction opcode dst input entry projected
  have accepted : runtime.bytecode.CompiledFunction.instruction_valid function instruction ⦃ result => result = true ⦄ := by
    unfold runtime.bytecode.CompiledFunction.instruction_valid
    simp only [scalar,load,store,projected,shape,bind_ok,uncurry_apply_pair]
    step as ⟨xy,xyEq⟩
    step as ⟨xyz,xyzEq⟩
    rw [slots_fit_accepts function input xyz (by scalar_tac)]
    simp only [bind_ok,↓reduceIte]
    rw [slots_fit_accepts function dst output destination]
    simp only [bind_ok,↓reduceIte,lift]
    simp only [bind_ok,WP.spec_ok,decide_eq_true_eq]
    scalar_tac
  obtain ⟨result,called,rfl⟩ := WP.spec_imp_exists accepted
  exact called

/-- Later emission, slot observations, and SIMD-table appends retain checking
of an earlier SIMD instruction. -/
theorem simd_instruction_monotone (before after : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (opcode dst input entry : U32)
    (projected : runtime.bytecode.Instr.simd instruction = .ok (some (opcode,dst,input,entry)))
    (capacity : before.slot_count.val ≤ after.slot_count.val)
    (table : before.simd.length ≤ after.simd.length)
    (accepted : runtime.bytecode.CompiledFunction.instruction_valid before instruction = .ok true) :
    runtime.bytecode.CompiledFunction.instruction_valid after instruction = .ok true := by
  obtain ⟨scalar,load,store⟩ := simd_view_disjoint instruction opcode dst input entry projected
  have called := accepted
  unfold runtime.bytecode.CompiledFunction.instruction_valid at called
  simp only [scalar,load,store,projected,bind_ok,uncurry_apply_pair] at called
  obtain ⟨shape,shapeRun,rest⟩ := bind_ok_inv _ _ _ called
  cases shape with
  | none => simp at rest
  | some shape =>
    obtain ⟨x,y,z,output⟩ := shape
    have bounds := simd_valid_bounds before instruction opcode dst input entry x y z output projected shapeRun accepted
    exact simd_instruction_accepts after instruction opcode dst input entry x y z output projected shapeRun
      (by omega) (by omega) (by omega)

end Itasca.Runtime.Compiler
