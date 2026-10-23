import Exec.Code.Local.Capacity.OperandBounds
import Exec.Code.Local.Relations.Global.GlobalLowering
set_option maxHeartbeats 1200000
namespace Exec.Code
open Aeneas Aeneas.Std

theorem global_get_valid_bounds (compiled : runtime.bytecode.CompiledFunction)
    (ty : valtype) (dst index : U32)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid compiled
      (globalGetInstruction (decide (width ty = 2)) dst index) = .ok true) :
    dst.val + width ty ≤ compiled.slot_count.val := by
  by_cases vector : width ty = 2
  · simp only [vector,decide_true,globalGetInstruction,ite_true] at checked
    simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,runtime.bytecode.Instr.scalar,runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok] at checked
    have bound := slots_fit_true compiled dst 2#u32 checked
    rw [vector]
    scalar_tac
  · have widthEq : width ty = 1 := by cases ty <;> simp_all [width]
    simp only [widthEq,globalGetInstruction,show decide (1=2) = false from rfl,Bool.false_eq_true,ite_false] at checked
    simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,runtime.bytecode.Instr.scalar,runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok] at checked
    have bound := slots_fit_true compiled dst 1#u32 checked
    rw [widthEq]
    scalar_tac

end Exec.Code
