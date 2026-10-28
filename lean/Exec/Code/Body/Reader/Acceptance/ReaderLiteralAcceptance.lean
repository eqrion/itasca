import Exec.Code.Local.Capacity.ReaderAcceptance
import Exec.Code.Local.Capacity.LiteralBudgetAvailability
import Itasca.Visitor.EventDispatch

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- The actual i32 hook accepts and charges at most one instruction. -/
theorem compiler_on_i32_const_available_effect {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (demand : CallbackDemand compiler state bound) (bits : I32) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_i32_const compiler state bits
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const,lift,bind_ok]
  exact compiler_literal_available_effect ops bound available compiler state demand .i32 _

/-- An independently accepted i32 reader is replayed with the same source
state, ordinary compiler acceptance, and a bounded instruction charge. -/
theorem compiler_reader_i32_const_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler final bound)
    (reference : code.step source st data env ctx code.OP_I32_CONST before =
      .ok (.Ok (),final,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_I32_CONST compiler ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = final ∧ CompilationBudgetEffect compiler.budget out.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [OpDispatch.dispatch_i32_const] at reference ⊢
  refine CoreVisitor.run.accepted_lift_on (code.read_i32_const st data) source.on_i32_const
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_i32_const
    before after compiler final
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  intro bits _ _
  exact compiler_on_i32_const_available_effect ops bound available compiler final demand bits

/-- The actual i64 hook accepts and charges at most one instruction. -/
theorem compiler_on_i64_const_available_effect {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (demand : CallbackDemand compiler state bound) (bits : I64) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_i64_const compiler state bits
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const,lift,bind_ok]
  exact compiler_literal_available_effect ops bound available compiler state demand .i64 _

/-- An independently accepted i64 reader is replayed with the same source
state, ordinary compiler acceptance, and a bounded instruction charge. -/
theorem compiler_reader_i64_const_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler final bound)
    (reference : code.step source st data env ctx code.OP_I64_CONST before =
      .ok (.Ok (),final,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_I64_CONST compiler ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = final ∧ CompilationBudgetEffect compiler.budget out.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [OpDispatch.dispatch_i64_const] at reference ⊢
  refine CoreVisitor.run.accepted_lift_on (code.read_i64_const st data) source.on_i64_const
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_i64_const
    before after compiler final
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  intro bits _ _
  exact compiler_on_i64_const_available_effect ops bound available compiler final demand bits

/-- The actual f32 hook accepts and charges at most one instruction. -/
theorem compiler_on_f32_const_available_effect {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (demand : CallbackDemand compiler state bound) (bits : U32) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_f32_const compiler state bits
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const,lift,bind_ok]
  exact compiler_literal_available_effect ops bound available compiler state demand .f32 _

/-- An independently accepted f32 reader is replayed with the same source
state, ordinary compiler acceptance, and a bounded instruction charge. -/
theorem compiler_reader_f32_const_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler final bound)
    (reference : code.step source st data env ctx code.OP_F32_CONST before =
      .ok (.Ok (),final,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_F32_CONST compiler ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = final ∧ CompilationBudgetEffect compiler.budget out.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [OpDispatch.dispatch_f32_const] at reference ⊢
  refine CoreVisitor.run.accepted_lift_on (code.read_f32_const st data) source.on_f32_const
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_f32_const
    before after compiler final
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  intro bits _ _
  exact compiler_on_f32_const_available_effect ops bound available compiler final demand bits

/-- The actual f64 hook accepts and charges at most one instruction. -/
theorem compiler_on_f64_const_available_effect {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (demand : CallbackDemand compiler state bound) (bits : U64) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_f64_const compiler state bits
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const,lift,bind_ok]
  exact compiler_literal_available_effect ops bound available compiler state demand .f64 _

/-- An independently accepted f64 reader is replayed with the same source
state, ordinary compiler acceptance, and a bounded instruction charge. -/
theorem compiler_reader_f64_const_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler final bound)
    (reference : code.step source st data env ctx code.OP_F64_CONST before =
      .ok (.Ok (),final,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_F64_CONST compiler ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = final ∧ CompilationBudgetEffect compiler.budget out.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [OpDispatch.dispatch_f64_const] at reference ⊢
  refine CoreVisitor.run.accepted_lift_on (code.read_f64_const st data) source.on_f64_const
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_f64_const
    before after compiler final
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  intro bits _ _
  exact compiler_on_f64_const_available_effect ops bound available compiler final demand bits

end Itasca.Runtime.Code
