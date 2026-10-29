import Itasca.Runtime.Compiler.Local.Capacity.ReaderAcceptance
import Itasca.Runtime.Compiler.Local.Capacity.GlobalAvailability
import Itasca.Runtime.Compiler.Local.Capacity.SelectAvailability
import Itasca.Runtime.Compiler.Local.Capacity.UnreachableAvailability
import Itasca.Visitor.EventDispatch
import Itasca.Runtime.Compiler.Body.Reader.Scalar.SelectTypes
import Itasca.Runtime.Compiler.Body.Reader.Global.GlobalEffects

/-!
Successful replay of simple scalar instructions from available callbacks and a reached reader point.
-/

/-! ## Reader Simple Acceptance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Replay the independent nop reader using bounded actual callback
acceptance, retaining the exact source result and all budget counters. -/
theorem compiler_reader_nop_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler final bound)
    (reference : code.step source st data env ctx code.OP_NOP before = .ok (.Ok (),final,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_NOP compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = final ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [OpDispatch.dispatch_nop] at reference ⊢
  refine CoreVisitor.run.accepted_lift_on (.ok (.Ok (),st)) (fun v state (_ : Unit) => source.on_nop v state) (fun v state (_ : Unit) => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_nop v state)
    before after compiler final
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  intro value _ _
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_nop]
  apply WP.spec_mono (compiler_nop_drop_available ops bound available compiler final demand false)
  intro result held
  rw [held.2]
  exact ⟨held.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

/-- Replay the independent drop reader using bounded actual callback
acceptance, retaining the exact source result and all budget counters. -/
theorem compiler_reader_drop_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler final bound)
    (reference : code.step source st data env ctx code.OP_DROP before = .ok (.Ok (),final,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_DROP compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = final ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [OpDispatch.dispatch_drop] at reference ⊢
  refine CoreVisitor.run.accepted_lift_on (code.read_drop st) source.on_drop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_drop
    before after compiler final
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  intro value _ _
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_drop]
  apply WP.spec_mono (compiler_nop_drop_available ops bound available compiler final demand true)
  intro result held
  rw [held.2]
  exact ⟨held.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

/-- Replay the independent unreachable reader using bounded actual callback
acceptance, retaining the exact source result and all budget counters. -/
theorem compiler_reader_unreachable_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler final bound)
    (reference : code.step source st data env ctx code.OP_UNREACHABLE before = .ok (.Ok (),final,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_UNREACHABLE compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = final ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [OpDispatch.dispatch_unreachable] at reference ⊢
  refine CoreVisitor.run.accepted_lift_on (code.read_unreachable st) (fun v state (_ : Unit) => source.on_unreachable v state) (fun v state (_ : Unit) => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_unreachable v state)
    before after compiler final
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  intro value _ _
  exact compiler_on_unreachable_available ops bound available compiler final demand

/-- Replay the independent global_get reader using bounded actual callback
acceptance, retaining the exact source result and all budget counters. -/
theorem compiler_reader_global_get_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler final bound)
    (reference : code.step source st data env ctx code.OP_GLOBAL_GET before = .ok (.Ok (),final,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_GLOBAL_GET compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = final ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [code.step_global_get.dispatch] at reference ⊢
  refine CoreVisitor.run.accepted_lift_on (code.read_global_get st data env) source.on_global_get (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_global_get
    before after compiler final
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  intro value _ _
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_global_get]
  exact compiler_global_get_available ops bound available compiler final demand value

/-- Replay the independent global_set reader using bounded actual callback
acceptance, retaining the exact source result and all budget counters. -/
theorem compiler_reader_global_set_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler final bound) (front : List valtype) (ty : valtype)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ [ty]))
    (reference : code.step source st data env ctx code.OP_GLOBAL_SET before = .ok (.Ok (),final,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_GLOBAL_SET compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = final ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [code.step_global_set.dispatch] at reference ⊢
  refine CoreVisitor.run.accepted_lift_on (code.read_global_set st data env) source.on_global_set (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_global_set
    before after compiler final
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  intro value _ _
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_global_set]
  exact compiler_global_set_available ops bound available compiler final demand value front ty layout

/-- Replay the independent select reader using bounded actual callback
acceptance, retaining the exact source result and all budget counters. -/
theorem compiler_reader_select_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler final bound) (front : List valtype) (ty : valtype)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ [ty,ty,.I32]))
    (reference : code.step source st data env ctx code.OP_SELECT before = .ok (.Ok (),final,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_SELECT compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = final ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [code.step_select.dispatch] at reference ⊢
  refine CoreVisitor.run.accepted_lift_on (code.read_select st) source.on_select (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_select
    before after compiler final
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  intro value _ _
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_select]
  exact compiler_select_available ops bound available compiler final demand front ty false layout

end Itasca.Runtime.Compiler

end

/-! ## Reached Simple Acceptance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- A checked source global write determines its exact declared operand type;
its compiler layout is derived from the retained complete source stack. -/
theorem reached_reader_global_set_available {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler out bound)
    (outer segment : List code.StackType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length)
    (monomorphic : compiler.reachable = true → Control.polymorphic st = false)
    (known : compiler.reachable = true → ConcreteStack st.vals.val)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.vals.val))
    (reference : code.step source st data env ctx code.OP_GLOBAL_SET before = .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_GLOBAL_SET compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · have raw := reference
    rw [code.step_global_set.dispatch] at raw
    obtain ⟨index,read,_⟩ := reader_run_success _ _ _ _ _ raw
    have currentKnown := (concrete_stack_append.mp (values ▸ known live)).2
    obtain ⟨ty,_,_,shape⟩ := reader_global_set_effect st out data env index outer segment values base
      (monomorphic live) currentKnown read
    have typed : Sequence.stackTypes st.vals.val = Sequence.stackTypes out.vals.val ++ [Translate.valueType ty.valtype] := by
      simp [shape,Sequence.stackTypes,Translate.valueType]
    have layout := wholeLayout live
    rw [typed] at layout
    exact compiler_reader_global_set_available ops bound available source before after compiler st out data env ctx
      demand (Sequence.stackTypes out.vals.val) (Translate.valueType ty.valtype) (fun _ => layout) reference
  · exact compiler_reader_global_set_available ops bound available source before after compiler st out data env ctx
      demand [] .I32 (fun impossible => False.elim (live impossible)) reference

/-- Live select operands follow from the independent reader's select effect,
including the final i32 condition. Dead code requires no live type layout. -/
theorem reached_reader_select_available {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler out bound) (capacity : st.vals.val.length < Usize.max)
    (outer segment : List code.StackType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length)
    (monomorphic : compiler.reachable = true → Control.polymorphic st = false)
    (known : compiler.reachable = true → ConcreteStack st.vals.val)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.vals.val))
    (reference : code.step source st data env ctx code.OP_SELECT before = .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_SELECT compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · have raw := reference
    rw [code.step_select.dispatch] at raw
    obtain ⟨selected,read,_⟩ := reader_run_success _ _ _ _ _ raw
    have checked := code.read_select.segment st outer segment values base capacity
    rw [read,WP.spec_ok] at checked
    obtain ⟨_,_,rest,new,_,effect⟩ := checked
    dsimp only at new effect
    rw [monomorphic live] at effect
    obtain ⟨ty,front,_,_,beforeTypes,_⟩ := select_full_stack_types (known live) values new effect
    have layout := wholeLayout live
    rw [beforeTypes] at layout
    exact compiler_reader_select_available ops bound available source before after compiler st out data env ctx
      demand front (Translate.valueType ty) (fun _ => layout) reference
  · exact compiler_reader_select_available ops bound available source before after compiler st out data env ctx
      demand [] .I32 (fun impossible => False.elim (live impossible)) reference

end Itasca.Runtime.Compiler

end
