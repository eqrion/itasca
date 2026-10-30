import Itasca.Visitor.ReaderAcceptance
import Itasca.Runtime.Compiler.Local.Capacity.FinishBudgetAvailability
import Itasca.Runtime.Compiler.Body.Reader.Scalar.IntegerFacts
import Itasca.Runtime.Compiler.Body.Reader.Float.FloatFacts
import Itasca.Visitor.EventDispatch
import Itasca.Runtime.Compiler.Body.Reader.Stacks.Values
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.ProfileAcceptance

/-!
Successful integer and floating-point reader replay at a reached source point. Local callback availability lifts to both accepted-reader and profile-filtered results.
-/

/-! ## Reader Numeric Acceptance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- Replaying an independently accepted base numeric instruction retains the
reader's exact source state and pays at most one instruction charge. -/
theorem compiler_reader_numeric_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler final bound) (front : List valtype)
    (op : SourceMachine.Numeric.Instruction) (base : (integerOpcode op).val < 192)
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
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler final bound) (front : List valtype)
    (op : SourceMachine.Float.Instruction) (base : (floatOpcode op).val < 256)
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

end Itasca.Runtime.Compiler

end

/-! ## Reached Numeric Acceptance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- The independently accepted Wasm 2 reader supplies the live operand
layout needed by numeric lowering. No accepted compiler callback is assumed. -/
theorem reached_reader_numeric_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (demand : CallbackDemand compiler out bound)
    (op : SourceMachine.Numeric.Instruction) (base : (integerOpcode op).val < 192)
    (capacity : st.core.vals.val.length < Usize.max)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (reference : code.step source st.core data env ⟨locals,p.ft.results⟩ (UScalar.cast .U8 (integerOpcode op)) before =
      .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st.core data env ⟨locals,p.ft.results⟩ (UScalar.cast .U8 (integerOpcode op)) compiler ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨operation,hook,meaning,handler,_,inputs,_⟩ := integer_reader_facts ops compiler out op base
    obtain ⟨_,_,_,_,values,effect,post⟩ := reader_numeric_wasm2 p source before after out _ operation hook
      capacity byte meaning handler reference
    rw [monomorphic live] at effect
    obtain ⟨old,new⟩ := post.values
    obtain ⟨front,_,oldTypes,_⟩ := numeric_full_stack_types (known live) old new effect
    rw [inputs] at oldTypes
    have layout := wholeLayout live
    rw [oldTypes] at layout
    exact compiler_reader_numeric_available ops bound available source before after compiler st.core out data env
      ⟨locals,p.ft.results⟩ demand front op base (fun _ => layout) reference
  · exact compiler_reader_numeric_available ops bound available source before after compiler st.core out data env
      ⟨locals,p.ft.results⟩ demand [] op base (fun impossible => False.elim (live impossible)) reference

/-- The independently accepted Wasm 2 reader supplies the live operand
layout needed by float lowering. No accepted compiler callback is assumed. -/
theorem reached_reader_float_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (demand : CallbackDemand compiler out bound)
    (op : SourceMachine.Float.Instruction) (base : (floatOpcode op).val < 256)
    (capacity : st.core.vals.val.length < Usize.max)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (floatOpcode op))
    (reference : code.step source st.core data env ⟨locals,p.ft.results⟩ (UScalar.cast .U8 (floatOpcode op)) before =
      .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st.core data env ⟨locals,p.ft.results⟩ (UScalar.cast .U8 (floatOpcode op)) compiler ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨operation,hook,meaning,handler,_,inputs,_⟩ := float_reader_facts ops compiler out op base
    obtain ⟨_,_,_,_,values,effect,post⟩ := reader_numeric_wasm2 p source before after out _ operation hook
      capacity byte meaning handler reference
    rw [monomorphic live] at effect
    obtain ⟨old,new⟩ := post.values
    obtain ⟨front,_,oldTypes,_⟩ := numeric_full_stack_types (known live) old new effect
    rw [inputs] at oldTypes
    have layout := wholeLayout live
    rw [oldTypes] at layout
    exact compiler_reader_float_available ops bound available source before after compiler st.core out data env
      ⟨locals,p.ft.results⟩ demand front op base (fun _ => layout) reference
  · exact compiler_reader_float_available ops bound available source before after compiler st.core out data env
      ⟨locals,p.ft.results⟩ demand [] op base (fun impossible => False.elim (live impossible)) reference

/-- The complete Wasm 2 profile dispatcher accepts this reached numeric
step, deriving its capacity check from independent reference acceptance. -/
theorem reached_profile_numeric_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (demand : CallbackDemand compiler out.core bound)
    (op : SourceMachine.Numeric.Instruction) (base : (integerOpcode op).val < 192)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (reference : code.step_profile source st data env ctx index .Wasm2
      (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (integerOpcode op)) compiler ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨_,_,_,_,_,_,_,_,ordinary,plain,sign,misc⟩ := integer_reader_facts ops compiler out.core op base
  obtain ⟨capacity,raw⟩ := profile_base_success_wasm2 source st out data env ctx ⟨locals,p.ft.results⟩
    index _ before after ordinary plain sign misc contextLocals reference
  exact profile_base_available_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out.core data env ctx ⟨locals,p.ft.results⟩ index _ compiler
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0))
    capacity ordinary plain sign misc contextLocals
    (reached_reader_numeric_available_wasm2 p ops bound available source before after compiler out.core demand
      op base capacity known monomorphic wholeLayout byte raw)

/-- The complete Wasm 2 profile dispatcher accepts this reached float
step, deriving its capacity check from independent reference acceptance. -/
theorem reached_profile_float_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (demand : CallbackDemand compiler out.core bound)
    (op : SourceMachine.Float.Instruction) (base : (floatOpcode op).val < 256)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (floatOpcode op))
    (reference : code.step_profile source st data env ctx index .Wasm2
      (UScalar.cast .U8 (floatOpcode op)) before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (floatOpcode op)) compiler ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨_,_,_,_,_,_,_,_,ordinary,plain,sign,misc⟩ := float_reader_facts ops compiler out.core op base
  obtain ⟨capacity,raw⟩ := profile_base_success_wasm2 source st out data env ctx ⟨locals,p.ft.results⟩
    index _ before after ordinary plain sign misc contextLocals reference
  exact profile_base_available_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out.core data env ctx ⟨locals,p.ft.results⟩ index _ compiler
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0))
    capacity ordinary plain sign misc contextLocals
    (reached_reader_float_available_wasm2 p ops bound available source before after compiler out.core demand
      op base capacity known monomorphic wholeLayout byte raw)

end Itasca.Runtime.Compiler

end
