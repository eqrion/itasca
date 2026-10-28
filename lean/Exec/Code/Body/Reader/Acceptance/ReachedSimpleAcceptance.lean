import Exec.Code.Body.Reader.Acceptance.ReaderSimpleAcceptance
import Exec.Code.Body.Reader.Common.ReaderSelectTypes
import Exec.Code.Body.Reader.Global.ReaderGlobalEffects

namespace Itasca.Runtime.Code
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
    have currentKnown := (concreteStack_append.mp (values ▸ known live)).2
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

end Itasca.Runtime.Code
