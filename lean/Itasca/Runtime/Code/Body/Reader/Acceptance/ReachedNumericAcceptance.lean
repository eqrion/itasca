import Itasca.Runtime.Code.Body.Reader.Acceptance.ReaderNumericAcceptance
import Itasca.Runtime.Code.Body.Reader.Common.ReaderValues
import Itasca.Runtime.Code.Body.Reader.Acceptance.ReaderProfileAcceptance

namespace Itasca.Runtime.Code
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
    (op : Abs.Numeric.Instruction) (base : (integerOpcode op).val < 192)
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
    (op : Abs.Float.Instruction) (base : (floatOpcode op).val < 256)
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
    (op : Abs.Numeric.Instruction) (base : (integerOpcode op).val < 192)
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
    (op : Abs.Float.Instruction) (base : (floatOpcode op).val < 256)
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

end Itasca.Runtime.Code
