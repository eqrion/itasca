import Itasca.Runtime.Code.Local.Lowering.Simd.SimdLowered
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- A checked SIMD subopcode has an exact, nonwrapping compiler opcode. -/
theorem simd_opcode_add (sub : U32) (opcode : U16) (bound : sub.val < 256)
    (number : opcode.val = 512+sub.val) :
    (512#u16 + UScalar.cast .U16 sub) = Result.ok opcode := by
  have cast : (UScalar.cast .U16 sub).val = sub.val := by
    rw [UScalar.cast_val_eq,Nat.mod_eq_of_lt (by norm_num; omega)]
  obtain ⟨actual,added,value⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := 512#u16) (y := UScalar.cast .U16 sub) (by scalar_tac))
  have equal : actual = opcode := by scalar_tac
  simpa only [equal] using added

variable {A : Type} (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
  (state : Itasca.code.OpIterState) (sub : U32) (opcode : U16)
  (bound : sub.val < 256) (number : opcode.val = 512+sub.val)

include bound number

theorem compiler_simd_callback :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd before state sub =
      runtime.compiler.lower.FunctionCompiler.op ops before state opcode 0#u32 0#u32 0#u128 := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_simd,lift,bind_ok,
    simd_opcode_add sub opcode bound number]

theorem compiler_simd_lane_callback (lane : U8) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_lane before state sub lane =
      runtime.compiler.lower.FunctionCompiler.op ops before state opcode
        (UScalar.cast .U32 lane) 0#u32 0#u128 := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_simd_lane,lift,bind_ok,
    simd_opcode_add sub opcode bound number]

theorem compiler_simd_memory_callback (arg : Itasca.code.MemArg) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_memory before state sub arg =
      runtime.compiler.lower.FunctionCompiler.op ops before state opcode arg.offset arg.align 0#u128 := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_simd_memory,lift,bind_ok,
    simd_opcode_add sub opcode bound number]

theorem compiler_simd_memory_lane_callback (arg : Itasca.code.MemArg) (lane : U8) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_memory_lane before state sub arg lane =
      runtime.compiler.lower.FunctionCompiler.op ops before state opcode arg.offset arg.align (UScalar.cast .U128 lane) := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_simd_memory_lane,lift,bind_ok,
    simd_opcode_add sub opcode bound number]

end Itasca.Runtime.Code
