import Exec.Code.Local.Capacity.ReaderAcceptance
import Exec.Code.Local.Capacity.FinishBudgetAvailability
import Exec.Code.Body.Reader.Common.NumericReaderFacts
import Exec.Code.Body.Reader.Float.FloatReaderFacts
import Itasca.Visitor.EventDispatch

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- Replaying an independently accepted base numeric instruction retains the
reader's exact source state and pays at most one instruction charge. -/
theorem compiler_reader_numeric_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler final bound) (front : List valtype)
    (op : Abs.Numeric.Instruction) (base : (integerOpcode op).val < 192)
    (layout : compiler.reachable = true →
      CompilerLayout compiler (front ++ List.replicate op.arity (integerType op.input)))
    (reference : code.step source st data env ctx (UScalar.cast .U8 (integerOpcode op)) before =
      .ok (.Ok (),final,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (integerOpcode op)) compiler ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = final ∧ CompilationBudgetEffect compiler.budget out.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨operation,hook,meaning,handler,rest⟩ := integer_reader_facts ops compiler st op base
  rw [dispatch_numeric _ st data env ctx before _ operation hook meaning handler] at reference
  rw [dispatch_numeric _ st data env ctx compiler _ operation hook meaning handler]
  refine CoreVisitor.run.accepted_lift_on (Numeric.read operation st)
    (fun v s (_ : Unit) => invoke source v (.op s (.numeric hook)))
    (fun v s (_ : Unit) => invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      v (.op s (.numeric hook))) before after compiler final
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  intro value _ _
  obtain ⟨operation',hook',meaning',handler',_,_,_,callback,_⟩ := integer_reader_facts ops compiler final op base
  have same : hook' = hook := Option.some.inj (handler'.symm.trans handler)
  subst hook'
  rw [callback]
  exact compiler_numeric_available_effect ops bound available compiler final demand front op layout

/-- Replaying an independently accepted base float instruction retains the
reader's exact source state and pays at most one instruction charge. -/
theorem compiler_reader_float_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler final bound) (front : List valtype)
    (op : Abs.Float.Instruction) (base : (floatOpcode op).val < 256)
    (layout : compiler.reachable = true →
      CompilerLayout compiler (front ++ List.replicate op.arity (valtype_numtype op.input)))
    (reference : code.step source st data env ctx (UScalar.cast .U8 (floatOpcode op)) before =
      .ok (.Ok (),final,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (floatOpcode op)) compiler ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = final ∧ CompilationBudgetEffect compiler.budget out.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨operation,hook,meaning,handler,rest⟩ := float_reader_facts ops compiler st op base
  rw [dispatch_numeric _ st data env ctx before _ operation hook meaning handler] at reference
  rw [dispatch_numeric _ st data env ctx compiler _ operation hook meaning handler]
  refine CoreVisitor.run.accepted_lift_on (Numeric.read operation st)
    (fun v s (_ : Unit) => invoke source v (.op s (.numeric hook)))
    (fun v s (_ : Unit) => invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      v (.op s (.numeric hook))) before after compiler final
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  intro value _ _
  obtain ⟨operation',hook',meaning',handler',_,_,_,callback,_⟩ := float_reader_facts ops compiler final op base
  have same : hook' = hook := Option.some.inj (handler'.symm.trans handler)
  subst hook'
  rw [callback]
  exact compiler_float_available_effect ops bound available compiler final demand front op layout

end Itasca.Runtime.Code
