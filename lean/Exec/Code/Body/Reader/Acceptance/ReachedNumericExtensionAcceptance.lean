import Exec.Code.Body.Reader.Acceptance.NumericPostAcceptance
import Exec.Code.Body.Reader.Acceptance.ReaderProfileAcceptance
import Exec.Code.Body.Reader.Common.ReaderSaturating
import Exec.Code.Local.Capacity.ReaderAcceptance

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- Every Wasm 2 sign extension accepts from the independently validated
reader effect and source-paid numeric demand. -/
theorem reached_profile_sign_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (op : Abs.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val)
    (demand : CallbackDemand compiler out.core bound)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (reference : code.step_profile source st data env ctx index .Wasm2 (UScalar.cast .U8 (integerOpcode op)) before =
      .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (integerOpcode op)) compiler ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨operation,hook,meaning,_,inputs,_,encoding,hookEq,ordinary,base⟩ :=
    integer_sign_reader_facts ops compiler out.core op extension
  obtain ⟨capacity,run⟩ := profile_scalar_success source st out data env ctx index _ before after ordinary reference
  rw [code.step_wasm2.base _ _ _ _ _ _ _ base] at run
  obtain ⟨_,_,converted,_,_,values,effect,post⟩ := reader_sign_wasm2 p source before after out.core ctx _ operation
    capacity byte meaning run
  have callback : code.visit_sign_extension (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      compiler out.core (UScalar.cast .U8 (integerOpcode op)) ⦃ result => result.1 = .Ok () ∧
        CompilationBudgetEffect compiler.budget result.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    have dispatch := ExtendedNumericHook.dispatch (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      compiler out.core hook
    rw [encoding] at dispatch
    dsimp only at dispatch
    rw [dispatch,hookEq]
    exact post.numeric_available effect ops bound available compiler demand op inputs known monomorphic wholeLayout
  apply profile_scalar_available_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out.core data env ctx index _ compiler
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) capacity ordinary
  rw [code.step_wasm2.base _ _ _ _ _ _ _ base,code.step_extended.sign _ _ _ _ _ _ _ _ meaning]
  exact CoreVisitor.run.available_of_read (code.read_conversion st.core operation.input operation.output)
    (fun v state (_ : Unit) => code.visit_sign_extension
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) v state (UScalar.cast .U8 (integerOpcode op)))
    compiler () out.core
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) converted callback

/-- Every saturating conversion accepts through its real prefix decoder and
source-validated conversion reader. Compilation assumes no native FP law. -/
theorem reached_profile_saturating_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (op : Abs.Float.Instruction) (extension : 256 ≤ (floatOpcode op).val)
    (subopcode : U32) (next : Usize) (subopcodeEq : subopcode.val = (floatOpcode op).val-256)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (demand : CallbackDemand compiler out.core bound)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = 0xfc#u8)
    (reference : code.step_profile source st data env ctx index .Wasm2 0xfc#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 0xfc#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨sub,operation,hook,subEq,small,meaning,_,inputs,_,encoding,hookEq⟩ :=
    float_saturating_reader_facts ops compiler out.core op extension
  have same : sub = subopcode := UScalar.eq_of_val_eq (subEq.trans subopcodeEq.symm)
  subst sub
  obtain ⟨capacity,run⟩ := profile_scalar_success source st out data env ctx index 0xfc#u8 before after (by decide) reference
  rw [code.step_wasm2.saturating _ _ _ _ _ _ _ _ decoded small] at run
  obtain ⟨_,_,converted,_,_,values,effect,post⟩ := reader_saturating_wasm2 p source before after out.core ctx subopcode next
    operation capacity byte decoded meaning run
  have callback : code.visit_saturating (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      compiler out.core subopcode ⦃ result => result.1 = .Ok () ∧
        CompilationBudgetEffect compiler.budget result.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    have dispatch := ExtendedNumericHook.dispatch (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      compiler out.core hook
    rw [encoding] at dispatch
    dsimp only at dispatch
    rw [dispatch,hookEq]
    exact post.float_available effect ops bound available compiler demand op inputs known monomorphic wholeLayout
  apply profile_scalar_available_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out.core data env ctx index 0xfc#u8 compiler
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) capacity (by decide)
  rw [code.step_wasm2.saturating _ _ _ _ _ _ _ _ decoded small,code.step_extended.prefixed]
  have readLeb := reader.read_u32_leb.complete data st.core.pos subopcode next decoded
  simp only [Wasm2.prefixedStep,readLeb,bind_ok,meaning]
  exact CoreVisitor.run.available_of_read (code.read_conversion {st.core with pos := next} operation.input operation.output)
    (fun v state (_ : Unit) => code.visit_saturating
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) v state subopcode) compiler () out.core
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) converted callback

end Itasca.Runtime.Code
