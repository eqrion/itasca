import Exec.Code.Local.Capacity.BudgetAvailability
import Exec.Code.Local.Lowering.Common.Emit

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- A representable bytecode PC excludes the actual instruction-index rejection. -/
theorem compiler_pc_available {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A)
    (bounded : compiler.function.code.length ≤ U32.max) :
    runtime.compiler.FunctionCompiler.pc ops compiler ⦃ out =>
      out.2 = compiler ∧ ∃ pc, out.1 = .Ok pc ∧ pc.val = compiler.function.code.length ⦄ := by
  unfold runtime.compiler.FunctionCompiler.pc
  step as ⟨maximum,maximumEq⟩
  have inside : ¬ alloc.vec.Vec.len compiler.function.code > maximum := by
    simp_all [core.num.U32.MAX,U32.rMax]
    scalar_tac
  simp only [if_neg inside]
  step as ⟨pc,pcEq⟩
  refine ⟨pc,rfl,?_⟩
  simp only [pcEq,UScalar.cast_val_eq]
  scalar_tac

end Itasca.Runtime.Code
