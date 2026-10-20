import Exec.Code.Local.Capacity.ReaderAcceptance
import Exec.Code.Local.Capacity.MemoryAvailability
import Exec.Code.Body.Reader.Memory.MemoryReaderFacts
import Itasca.Visitor.EventDispatch

namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Every scalar and packed load replays the independent reader result
and accepts with at most one instruction charge, including dead code. -/
theorem compiler_reader_memory_load_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler final bound) (front : List valtype)
    (op : Abs.Memory.Load)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ [.I32]))
    (reference : code.step source st data env ctx (UScalar.cast .U8 (memoryLoadOpcode op)) before =
      .ok (.Ok (),final,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (memoryLoadOpcode op)) compiler ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = final ∧ CompilationBudgetEffect compiler.budget out.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  have facts := memory_load_reader_facts ops compiler st op ⟨0#u32,0#u32⟩
  rw [code.step_memory.dispatch _ st data env ctx before _ _ facts.1,facts.2.1] at reference
  rw [code.step_memory.dispatch _ st data env ctx compiler _ _ facts.1,facts.2.1]
  simp only [Bool.false_eq_true,↓reduceIte] at reference ⊢
  refine CoreVisitor.run.accepted_lift_on (code.read_load st data env _ _)
    (fun v state arg => code.visit_memory source v state (UScalar.cast .U8 (memoryLoadOpcode op)) arg)
    (fun v state arg => code.visit_memory (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      v state (UScalar.cast .U8 (memoryLoadOpcode op)) arg) before after compiler final
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  intro arg _ _
  rw [(memory_load_reader_facts ops compiler final op arg).2.2.2.2.1]
  exact compiler_memory_load_available ops bound available compiler final demand front op arg.offset arg.align layout

/-- Every scalar and packed store replays the independent reader result
and accepts with at most one instruction charge, including dead code. -/
theorem compiler_reader_memory_store_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler final bound) (front : List valtype)
    (op : Abs.Memory.Store)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ [.I32,valtype_numtype op.type]))
    (reference : code.step source st data env ctx (UScalar.cast .U8 (memoryStoreOpcode op)) before =
      .ok (.Ok (),final,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (memoryStoreOpcode op)) compiler ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = final ∧ CompilationBudgetEffect compiler.budget out.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  have facts := memory_store_reader_facts ops compiler st op ⟨0#u32,0#u32⟩
  rw [code.step_memory.dispatch _ st data env ctx before _ _ facts.1,facts.2.1] at reference
  rw [code.step_memory.dispatch _ st data env ctx compiler _ _ facts.1,facts.2.1]
  simp only [↓reduceIte] at reference ⊢
  refine CoreVisitor.run.accepted_lift_on (code.read_store st data env _ _)
    (fun v state arg => code.visit_memory source v state (UScalar.cast .U8 (memoryStoreOpcode op)) arg)
    (fun v state arg => code.visit_memory (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      v state (UScalar.cast .U8 (memoryStoreOpcode op)) arg) before after compiler final
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  intro arg _ _
  rw [(memory_store_reader_facts ops compiler final op arg).2.2.2.2.1]
  exact compiler_memory_store_available ops bound available compiler final demand front op arg.offset arg.align layout

end Exec.Code
