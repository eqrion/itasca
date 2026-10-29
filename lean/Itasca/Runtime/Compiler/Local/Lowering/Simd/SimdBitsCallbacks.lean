import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdCallbacks
import Itasca.Runtime.Compiler.Local.Initializer
namespace Itasca.Runtime.Code
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
end Itasca.Runtime.Code
