import Itasca.Runtime.Compiler.Local.Capacity.FinishBudgetAvailability
import Itasca.Runtime.Compiler.Local.Relations.Memory.MemoryEmission

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Every scalar/packed load callback accepts from its typed address layout
and independent resource demand. Compilation touches no memory buffer. -/
theorem compiler_memory_load_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (front : List valtype)
    (op : Abs.Memory.Load) (offset alignment : U32)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ [.I32])) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (memoryLoadOpcode op) offset alignment 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨address,read,_⟩ := memory_load_operand ops compiler front (layout live)
    rw [lower_memory_load_eq ops compiler state op offset alignment address live read]
    exact finish_op_available_effect ops bound available compiler state demand _
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg live]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

/-- Every scalar/packed store callback has the same acceptance and resource
bound, including f32/f64 and both integer widths. -/
theorem compiler_memory_store_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (front : List valtype)
    (op : Abs.Memory.Store) (offset alignment : U32)
    (layout : compiler.reachable = true →
      CompilerLayout compiler (front ++ [.I32,valtype_numtype op.type])) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (memoryStoreOpcode op) offset alignment 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨address,value,addressRead,valueRead,_,_⟩ := memory_store_operands ops compiler front op.type (layout live)
    rw [lower_memory_store_eq ops compiler state op offset alignment address value live addressRead valueRead]
    exact finish_op_available_effect ops bound available compiler state demand _
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg live]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Runtime.Code
