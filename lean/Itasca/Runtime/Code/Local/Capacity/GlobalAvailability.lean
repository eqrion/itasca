import Itasca.Runtime.Code.Local.Capacity.FinishBudgetAvailability
import Itasca.Runtime.Code.Local.Relations.Global.GlobalSafety
import Itasca.Runtime.Code.Local.Lowering.Local.LoweringLocal

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Global reads accept for every observed stack, including unreachable code
and vector-valued globals, under independent compilation demand. -/
theorem compiler_global_get_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (index : U32) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 35#u16 index 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨wide,top,_⟩ := WP.spec_imp_exists (top_is_v128_total state.vals.deref)
    rw [lower_global_get_eq ops compiler state index wide live top]
    exact finish_op_available_effect ops bound available compiler state demand _
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg live]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

/-- Global writes accept from the independently typed operand layout. The
height subtraction is justified by that layout, rather than assumed normal. -/
theorem compiler_global_set_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (index : U32)
    (front : List valtype) (ty : valtype)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ [ty])) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 36#u16 index 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨source,read,position⟩ := last_operand ops compiler front ty (layout live)
    have height := (layout live).height
    simp only [slots_append,slots,Nat.add_zero] at height
    obtain ⟨difference,subtract,_⟩ := WP.spec_imp_exists
      (UScalar.sub_spec (x := compiler.height) (y := source) (by omega))
    rw [lower_global_set_eq ops compiler state index source difference live read subtract]
    exact finish_op_available_effect ops bound available compiler state demand _
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg live]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Runtime.Code
