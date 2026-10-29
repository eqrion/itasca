import Itasca.Runtime.Compiler.Local.Capacity.ReaderAcceptance
import Itasca.Runtime.Compiler.Local.Capacity.LocalVariableAvailability
import Itasca.Runtime.Compiler.Local.Capacity.DeadOpAvailability
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEffects

/-!
Independently accepted local.get reading supplies the declared type and live operand shape. It needs no successful compiler callback premise.

Main declarations: `compiler_reader_local_get_available` and `compiler_reader_local_tee_available`. A direct consumer is `Compiler.Body.Reader.Acceptance.ScalarAcceptance`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Independently accepted local.get reading supplies the declared type
and live operand shape. It needs no successful compiler callback premise. -/
theorem compiler_reader_local_get_available {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler out bound) (localsMatch : compiler.function.locals = ctx.locals)
    (capacity : st.vals.val.length < Usize.max)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.vals.val))
    (reference : code.step source st data env ctx code.OP_LOCAL_GET before = .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOCAL_GET compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [code.step_local_get.dispatch] at reference ⊢
  obtain ⟨index,read,_⟩ := reader_run_success _ _ _ _ _ reference
  have callback : (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_local_get compiler out index ⦃ result =>
      result.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget result.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    change runtime.compiler.lower.FunctionCompiler.op ops compiler out 32#u16 index 0#u32 0#u128 ⦃ _ ⦄
    by_cases live : compiler.reachable = true
    · obtain ⟨ty,found,_⟩ := reader_local_get_effect st out data ctx index capacity read
      exact compiler_local_variable_available ops bound available compiler out demand (Sequence.stackTypes st.vals.val)
        index ty false false (fun _ => wholeLayout live) (fun _ => by simpa [localsMatch] using found)
    · apply WP.spec_mono (compiler_dead_op_available ops bound available compiler out 32#u16 index 0#u32
        0#u128 live demand.operands demand.slots)
      intro result held
      rw [held.2]
      exact ⟨held.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩
  exact CoreVisitor.run.available_of_read (code.read_local_get st data ctx)
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_local_get compiler index out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) read callback

/-- Independently accepted local.set reading supplies the declared type
and live operand shape. It needs no successful compiler callback premise. -/
theorem compiler_reader_local_set_available {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler out bound) (localsMatch : compiler.function.locals = ctx.locals)
    (capacity : st.vals.val.length < Usize.max)
    (outer segment : List code.StackType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length)
    (monomorphic : compiler.reachable = true → Control.polymorphic st = false)
    (known : compiler.reachable = true → ConcreteStack st.vals.val)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.vals.val))
    (reference : code.step source st data env ctx code.OP_LOCAL_SET before = .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOCAL_SET compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [code.step_local_set.dispatch] at reference ⊢
  obtain ⟨index,read,_⟩ := reader_run_success _ _ _ _ _ reference
  have callback : (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_local_set compiler out index ⦃ result =>
      result.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget result.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    change runtime.compiler.lower.FunctionCompiler.op ops compiler out 33#u16 index 0#u32 0#u128 ⦃ _ ⦄
    by_cases live : compiler.reachable = true
    · have currentKnown : ConcreteStack segment := (concreteStack_append.mp (values ▸ known live)).2
      obtain ⟨ty,found,shape⟩ := reader_local_set_effect st out data ctx index outer segment values base
        (monomorphic live) currentKnown read
      have typed : Sequence.stackTypes st.vals.val = Sequence.stackTypes out.vals.val ++ [Translate.valueType ty] := by
        simp [shape,Sequence.stackTypes,Translate.valueType]
      have layout := wholeLayout live
      rw [typed] at layout
      exact compiler_local_variable_available ops bound available compiler out demand (Sequence.stackTypes out.vals.val)
        index ty true false (fun _ => layout) (fun _ => by simpa [localsMatch] using found)
    · apply WP.spec_mono (compiler_dead_op_available ops bound available compiler out 33#u16 index 0#u32
        0#u128 live demand.operands demand.slots)
      intro result held
      rw [held.2]
      exact ⟨held.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩
  exact CoreVisitor.run.available_of_read (code.read_local_set st data ctx)
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_local_set compiler index out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) read callback

/-- Independently accepted local.tee reading supplies the declared type
and live operand shape. It needs no successful compiler callback premise. -/
theorem compiler_reader_local_tee_available {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler out bound) (localsMatch : compiler.function.locals = ctx.locals)
    (capacity : st.vals.val.length < Usize.max)
    (outer segment : List code.StackType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length)
    (monomorphic : compiler.reachable = true → Control.polymorphic st = false)
    (known : compiler.reachable = true → ConcreteStack st.vals.val)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.vals.val))
    (reference : code.step source st data env ctx code.OP_LOCAL_TEE before = .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOCAL_TEE compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [code.step_local_tee.dispatch] at reference ⊢
  obtain ⟨index,read,_⟩ := reader_run_success _ _ _ _ _ reference
  have callback : (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_local_tee compiler out index ⦃ result =>
      result.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget result.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    change runtime.compiler.lower.FunctionCompiler.op ops compiler out 34#u16 index 0#u32 0#u128 ⦃ _ ⦄
    by_cases live : compiler.reachable = true
    · have currentKnown : ConcreteStack segment := (concreteStack_append.mp (values ▸ known live)).2
      obtain ⟨ty,found,rest,shape,_⟩ := reader_local_tee_effect st out data ctx index capacity outer segment values base
        (monomorphic live) currentKnown read
      have typed : Sequence.stackTypes st.vals.val = Sequence.stackTypes rest ++ [Translate.valueType ty] := by
        simp [shape,Sequence.stackTypes,Translate.valueType]
      have layout := wholeLayout live
      rw [typed] at layout
      exact compiler_local_variable_available ops bound available compiler out demand (Sequence.stackTypes rest)
        index ty true true (fun _ => layout) (fun _ => by simpa [localsMatch] using found)
    · apply WP.spec_mono (compiler_dead_op_available ops bound available compiler out 34#u16 index 0#u32
        0#u128 live demand.operands demand.slots)
      intro result held
      rw [held.2]
      exact ⟨held.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩
  exact CoreVisitor.run.available_of_read (code.read_local_tee st data ctx)
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_local_tee compiler index out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) read callback

end Itasca.Runtime.Code
