import Itasca.Runtime.Code.Local.Capacity.FinishBudgetAvailability
import Itasca.Runtime.Code.Local.Relations.Common.SelectOperands

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Both forms of select accept scalar, reference, or vector layouts, with
one instruction of budget and no charge to other compiler counters. -/
theorem compiler_select_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (front : List valtype) (ty : valtype)
    (typed : Bool)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ [ty,ty,.I32])) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (if typed then 28#u16 else 27#u16) 0#u32 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨left,right,condition,hl,hr,hc,_,position,_⟩ := select_operands ops compiler front ty (layout live)
    obtain ⟨difference,subtract,_⟩ := WP.spec_imp_exists
      (UScalar.sub_spec (x := right) (y := left) (by omega))
    rw [lower_select_eq ops compiler state left right condition difference typed live hl hr hc subtract]
    exact finish_op_available_effect ops bound available compiler state demand _
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg live]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

/-- Nop and drop only observe the stack, irrespective of reachability. -/
theorem compiler_nop_drop_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (drop : Bool) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (if drop then 26#u16 else 1#u16) 0#u32 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ∧ out.2.budget = compiler.budget ⦄ := by
  have dispatch : runtime.compiler.lower.FunctionCompiler.op ops compiler state
      (if drop then 26#u16 else 1#u16) 0#u32 0#u32 0#u128 =
      runtime.compiler.FunctionCompiler.observe ops compiler state := by
    cases drop <;> unfold runtime.compiler.lower.FunctionCompiler.op <;> split <;> rfl
  rw [dispatch]
  exact compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots

end Itasca.Runtime.Code
