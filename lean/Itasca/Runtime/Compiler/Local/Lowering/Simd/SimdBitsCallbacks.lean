import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdDispatch
import Itasca.Runtime.Compiler.Local.Initializer

/-!
Sections, each formerly its own module: SimdStaticTables, SimdCallbacks, SimdBitsCallbacks.
-/

/-! ## SimdStaticTables -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

theorem compiler_simd_preserved_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a : U32) (bits : U128)
    (accepted : runtime.compiler.simd.FunctionCompiler.simd_op ops before state opcode a bits = .ok (.Ok (),after)) :
    after.function.indirect.val = before.function.indirect.val ∧
      after.function.jump_tables.val = before.function.jump_tables.val := by
  unfold runtime.compiler.simd.FunctionCompiler.simd_op at accepted
  repeat' table_preservation_step accepted using ops, law

theorem compiler_lower_simd_preserved_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (lower : 512 ≤ opcode.val) (upper : opcode.val < 768)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    after.function.indirect.val = before.function.indirect.val ∧
      after.function.jump_tables.val = before.function.jump_tables.val := by
  by_cases reachable : before.reachable = true
  · rw [lower_simd_dispatch ops before state opcode a b bits reachable lower upper] at accepted
    exact compiler_simd_preserved_tables ops law before after state opcode a bits accepted
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reachable] at accepted
    have tables := compiler_observe_tables ops law before after state (.Ok ()) accepted
    exact ⟨congrArg CompilerTables.indirect tables,congrArg CompilerTables.jumpTables tables⟩
end Itasca.Runtime.Compiler

end

/-! ## SimdCallbacks -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## SimdBitsCallbacks -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

theorem compiler_simd_constant_callback {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (lo hi : U64) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_const before state lo hi =
      runtime.compiler.lower.FunctionCompiler.op ops before state 524#u16 0#u32 0#u32 (initializerBits lo hi) := by
  have shift : (UScalar.cast .U128 hi <<< 64#i32) = .ok (⟨(UScalar.cast .U128 hi).bv <<< 64⟩ : U128) := rfl
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_simd_const,lift,bind_ok,shift]
  rfl

theorem compiler_simd_shuffle_callback {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (lo hi : U64) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_shuffle before state lo hi =
      runtime.compiler.lower.FunctionCompiler.op ops before state 525#u16 0#u32 0#u32 (initializerBits lo hi) := by
  have shift : (UScalar.cast .U128 hi <<< 64#i32) = .ok (⟨(UScalar.cast .U128 hi).bv <<< 64⟩ : U128) := rfl
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_simd_shuffle,lift,bind_ok,shift]
  rfl
end Itasca.Runtime.Compiler

end
