import Exec.Code.Local.Capacity.SimdOpAvailability
import Exec.Code.Local.Lowering.Simd.SimdBitsCallbacks

namespace Exec.Code
open Aeneas Aeneas.Std

/-- The actual SIMD visitor hook accepts its independently meaningful opcode
and bounded metadata request, including unreachable paths. -/
theorem compiler_on_simd_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (C : context)
    (front input output : List valtype) (source : instr)
    (opcode : U16) (sub : U32)
    (number : opcode.val = 512+sub.val) (bounded : sub.val < 256) (nonconstant : sub.val ≠ 12)
    (meaning : SimdImmediateMeaning C sub (simdImmediate sub 0#u32 0#u128) input source output)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ input))
    (postLength : compiler.reachable = true → state.vals.val.length = (front ++ output).length)
    (operandCapacity : compiler.before.length < Usize.max)
    (tableBound : compiler.function.simd.length ≤ compiler.function.code.length) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd compiler state sub ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [compiler_simd_callback ops compiler state sub opcode bounded number]
  exact compiler_simd_nonconstant_op_available ops bound available compiler state demand C front input output source
    opcode sub 0#u32 0#u32 0#u128 number bounded nonconstant meaning layout postLength operandCapacity tableBound

/-- The actual SIMD visitor hook accepts its independently meaningful opcode
and bounded metadata request, including unreachable paths. -/
theorem compiler_on_simd_lane_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (C : context)
    (front input output : List valtype) (source : instr)
    (opcode : U16) (sub : U32) (lane : U8)
    (number : opcode.val = 512+sub.val) (bounded : sub.val < 256) (nonconstant : sub.val ≠ 12)
    (meaning : SimdImmediateMeaning C sub (simdImmediate sub (UScalar.cast .U32 lane) 0#u128) input source output)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ input))
    (postLength : compiler.reachable = true → state.vals.val.length = (front ++ output).length)
    (operandCapacity : compiler.before.length < Usize.max)
    (tableBound : compiler.function.simd.length ≤ compiler.function.code.length) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_lane compiler state sub lane ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [compiler_simd_lane_callback ops compiler state sub opcode bounded number lane]
  exact compiler_simd_nonconstant_op_available ops bound available compiler state demand C front input output source
    opcode sub (UScalar.cast .U32 lane) 0#u32 0#u128 number bounded nonconstant meaning layout postLength operandCapacity tableBound

/-- The actual SIMD visitor hook accepts its independently meaningful opcode
and bounded metadata request, including unreachable paths. -/
theorem compiler_on_simd_memory_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (C : context)
    (front input output : List valtype) (source : instr)
    (opcode : U16) (sub : U32) (arg : Itasca.code.MemArg)
    (number : opcode.val = 512+sub.val) (bounded : sub.val < 256) (nonconstant : sub.val ≠ 12)
    (meaning : SimdImmediateMeaning C sub (simdImmediate sub arg.offset 0#u128) input source output)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ input))
    (postLength : compiler.reachable = true → state.vals.val.length = (front ++ output).length)
    (operandCapacity : compiler.before.length < Usize.max)
    (tableBound : compiler.function.simd.length ≤ compiler.function.code.length) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_memory compiler state sub arg ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [compiler_simd_memory_callback ops compiler state sub opcode bounded number arg]
  exact compiler_simd_nonconstant_op_available ops bound available compiler state demand C front input output source
    opcode sub arg.offset arg.align 0#u128 number bounded nonconstant meaning layout postLength operandCapacity tableBound

/-- The actual SIMD visitor hook accepts its independently meaningful opcode
and bounded metadata request, including unreachable paths. -/
theorem compiler_on_simd_memory_lane_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (C : context)
    (front input output : List valtype) (source : instr)
    (opcode : U16) (sub : U32) (arg : Itasca.code.MemArg) (lane : U8)
    (number : opcode.val = 512+sub.val) (bounded : sub.val < 256) (nonconstant : sub.val ≠ 12)
    (meaning : SimdImmediateMeaning C sub (simdImmediate sub arg.offset (UScalar.cast .U128 lane)) input source output)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ input))
    (postLength : compiler.reachable = true → state.vals.val.length = (front ++ output).length)
    (operandCapacity : compiler.before.length < Usize.max)
    (tableBound : compiler.function.simd.length ≤ compiler.function.code.length) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_memory_lane compiler state sub arg lane ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [compiler_simd_memory_lane_callback ops compiler state sub opcode bounded number arg lane]
  exact compiler_simd_nonconstant_op_available ops bound available compiler state demand C front input output source
    opcode sub arg.offset arg.align (UScalar.cast .U128 lane) number bounded nonconstant meaning layout postLength operandCapacity tableBound

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

/-- Shuffle uses its checked independent immediate meaning and the same
metadata ledger as the other nonconstant SIMD callbacks. -/
theorem compiler_on_simd_shuffle_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (C : context)
    (front input output : List valtype) (source : instr) (lo hi : U64)
    (meaning : SimdImmediateMeaning C 13#u32 (simdImmediate 13#u32 0#u32 (initializerBits lo hi)) input source output)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ input))
    (postLength : compiler.reachable = true → state.vals.val.length = (front ++ output).length)
    (operandCapacity : compiler.before.length < Usize.max)
    (tableBound : compiler.function.simd.length ≤ compiler.function.code.length) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_shuffle compiler state lo hi ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [compiler_simd_shuffle_callback ops compiler state lo hi]
  exact compiler_simd_nonconstant_op_available ops bound available compiler state demand C front input output source
    525#u16 13#u32 0#u32 0#u32 (initializerBits lo hi) (by decide) (by decide) (by decide)
    meaning layout postLength operandCapacity tableBound

end Exec.Code
