import Exec.Code.Local.Capacity.SimdOpAvailability
import Exec.Code.Local.Lowering.Simd.SimdBitsCallbacks

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

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

end Itasca.Runtime.Code
