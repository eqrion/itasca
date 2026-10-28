import Itasca.Runtime.Code.Local.Lowering.Simd.SimdSafety
import Itasca.Runtime.Code.Local.Lowering.Simd.SimdBitsCallbacks

/-! Normal return of every SIMD compiler callback from the actual visitor. -/
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

@[step] theorem compiler_on_simd_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (sub : U32) (bound : sub.val < 256)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (poolFits : compiler.function.v128_pool.val.length < Usize.max)
    (tableFits : compiler.function.simd.val.length < Usize.max) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd compiler state sub ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  let opcode : U16 := UScalar.ofNatCore (512 + sub.val) (by scalar_tac)
  have number : opcode.val = 512 + sub.val := rfl
  rw [compiler_simd_callback ops compiler state sub opcode bound number]
  exact compiler_simd_total ops law compiler state opcode _ _ _ (by omega) (by omega)
    codeFits sourceFits coordinateFits poolFits tableFits

@[step] theorem compiler_on_simd_lane_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (sub : U32) (lane : U8) (bound : sub.val < 256)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (poolFits : compiler.function.v128_pool.val.length < Usize.max)
    (tableFits : compiler.function.simd.val.length < Usize.max) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_lane compiler state sub lane ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  let opcode : U16 := UScalar.ofNatCore (512 + sub.val) (by scalar_tac)
  have number : opcode.val = 512 + sub.val := rfl
  rw [compiler_simd_lane_callback ops compiler state sub opcode bound number lane]
  exact compiler_simd_total ops law compiler state opcode _ _ _ (by omega) (by omega)
    codeFits sourceFits coordinateFits poolFits tableFits

@[step] theorem compiler_on_simd_memory_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (sub : U32) (arg : Itasca.code.MemArg) (bound : sub.val < 256)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (poolFits : compiler.function.v128_pool.val.length < Usize.max)
    (tableFits : compiler.function.simd.val.length < Usize.max) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_memory compiler state sub arg ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  let opcode : U16 := UScalar.ofNatCore (512 + sub.val) (by scalar_tac)
  have number : opcode.val = 512 + sub.val := rfl
  rw [compiler_simd_memory_callback ops compiler state sub opcode bound number arg]
  exact compiler_simd_total ops law compiler state opcode _ _ _ (by omega) (by omega)
    codeFits sourceFits coordinateFits poolFits tableFits

@[step] theorem compiler_on_simd_memory_lane_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (sub : U32) (arg : Itasca.code.MemArg) (lane : U8) (bound : sub.val < 256)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (poolFits : compiler.function.v128_pool.val.length < Usize.max)
    (tableFits : compiler.function.simd.val.length < Usize.max) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_memory_lane compiler state sub arg lane ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  let opcode : U16 := UScalar.ofNatCore (512 + sub.val) (by scalar_tac)
  have number : opcode.val = 512 + sub.val := rfl
  rw [compiler_simd_memory_lane_callback ops compiler state sub opcode bound number arg lane]
  exact compiler_simd_total ops law compiler state opcode _ _ _ (by omega) (by omega)
    codeFits sourceFits coordinateFits poolFits tableFits

@[step] theorem compiler_on_simd_const_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (lo hi : U64)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (poolFits : compiler.function.v128_pool.val.length < Usize.max)
    (tableFits : compiler.function.simd.val.length < Usize.max) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_const compiler state lo hi ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  rw [compiler_simd_constant_callback ops compiler state lo hi]
  exact compiler_simd_total ops law compiler state _ _ _ _ (by decide) (by decide)
    codeFits sourceFits coordinateFits poolFits tableFits

@[step] theorem compiler_on_simd_shuffle_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (lo hi : U64)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (poolFits : compiler.function.v128_pool.val.length < Usize.max)
    (tableFits : compiler.function.simd.val.length < Usize.max) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_shuffle compiler state lo hi ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  rw [compiler_simd_shuffle_callback ops compiler state lo hi]
  exact compiler_simd_total ops law compiler state _ _ _ _ (by decide) (by decide)
    codeFits sourceFits coordinateFits poolFits tableFits

end Itasca.Runtime.Code
