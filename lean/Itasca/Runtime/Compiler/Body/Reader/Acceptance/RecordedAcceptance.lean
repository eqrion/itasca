import Itasca.Runtime.Compiler.Local.Callbacks.CallbackEquations
import Itasca.Visitor.BodyReplay
import Itasca.Runtime.Compiler.Local.Capacity.GlobalAvailability
import Itasca.Runtime.Compiler.Local.Capacity.UnreachableAvailability
import Itasca.Runtime.Compiler.Body.Reader.Scalar.Unreachable
import Itasca.Runtime.Compiler.Body.Reader.Global.GlobalEmissions
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulPost
import Itasca.Runtime.Compiler.Local.Capacity.CallAvailability
import Itasca.Runtime.Compiler.Local.Relations.Calls.StatefulCallbacks
import Itasca.Visitor.Events
import Itasca.Visitor.RunTrace

/-!
Sections, each formerly its own module: LiteralAcceptance, ReachedSimpleAcceptance, ScalarAcceptance, StatefulCallbackAcceptance, RecordedAcceptance.
-/

/-! ## LiteralAcceptance -/

section

/-!
The actual i32 hook accepts and charges at most one instruction.

Main declarations: `compiler_on_i32_const_available_effect` and `compiler_reader_f64_const_available`. A direct consumer is `Compiler.Body.Reader.Acceptance.ScalarAcceptance`.
-/

namespace Itasca.Runtime.Compiler
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
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_i32_const.eq,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const.eq,lift,bind_ok]
  exact compiler_literal_available_effect ops bound available compiler state demand .i32 _

/-- An independently accepted i32 reader is replayed with the same source
state, ordinary compiler acceptance, and a bounded instruction charge. -/
theorem compiler_reader_i32_const_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
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
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_i64_const.eq,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const.eq,lift,bind_ok]
  exact compiler_literal_available_effect ops bound available compiler state demand .i64 _

/-- An independently accepted i64 reader is replayed with the same source
state, ordinary compiler acceptance, and a bounded instruction charge. -/
theorem compiler_reader_i64_const_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
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
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_f32_const.eq,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const.eq,lift,bind_ok]
  exact compiler_literal_available_effect ops bound available compiler state demand .f32 _

/-- An independently accepted f32 reader is replayed with the same source
state, ordinary compiler acceptance, and a bounded instruction charge. -/
theorem compiler_reader_f32_const_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
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
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_f64_const.eq,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const.eq,lift,bind_ok]
  exact compiler_literal_available_effect ops bound available compiler state demand .f64 _

/-- An independently accepted f64 reader is replayed with the same source
state, ordinary compiler acceptance, and a bounded instruction charge. -/
theorem compiler_reader_f64_const_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
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

end Itasca.Runtime.Compiler

end

/-! ## ReachedSimpleAcceptance -/

section

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
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
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
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_nop.eq,
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
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
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
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_drop.eq,
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
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
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
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
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
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_global_get.eq,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_global_get]
  exact compiler_global_get_available ops bound available compiler final demand value

/-- Replay the independent global_set reader using bounded actual callback
acceptance, retaining the exact source result and all budget counters. -/
theorem compiler_reader_global_set_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
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
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_global_set.eq,
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_global_set]
  exact compiler_global_set_available ops bound available compiler final demand value front ty layout

/-- Replay the independent select reader using bounded actual callback
acceptance, retaining the exact source result and all budget counters. -/
theorem compiler_reader_select_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
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
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_select.eq,
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
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
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
    obtain ⟨index,read,_⟩ := CoreVisitor.run.accepted _ _ _ _ _ raw
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
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
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
    obtain ⟨selected,read,_⟩ := CoreVisitor.run.accepted _ _ _ _ _ raw
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

end

/-! ## ScalarAcceptance -/

section

/-!
The ordinary scalar readers whose source parsing and callback acceptance are independent of prefix decoding and structured-control dispatch.

Main declarations: `ScalarReaderKind` and `opcode`. A direct consumer is `Compiler.Body.Reader.Acceptance.SourceBoundScalarAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- The ordinary scalar readers whose source parsing and callback acceptance
are independent of prefix decoding and structured-control dispatch. -/
inductive ScalarReaderKind where
  | nop
  | unreachable
  | drop
  | select
  | local_get
  | local_set
  | local_tee
  | global_get
  | global_set
  | i32_const
  | i64_const
  | f32_const
  | f64_const

namespace ScalarReaderKind

def opcode : ScalarReaderKind → U8
  | .nop => code.OP_NOP
  | .unreachable => code.OP_UNREACHABLE
  | .drop => code.OP_DROP
  | .select => code.OP_SELECT
  | .local_get => code.OP_LOCAL_GET
  | .local_set => code.OP_LOCAL_SET
  | .local_tee => code.OP_LOCAL_TEE
  | .global_get => code.OP_GLOBAL_GET
  | .global_set => code.OP_GLOBAL_SET
  | .i32_const => code.OP_I32_CONST
  | .i64_const => code.OP_I64_CONST
  | .f32_const => code.OP_F32_CONST
  | .f64_const => code.OP_F64_CONST

def Parameter : ScalarReaderKind → Type
  | .nop => Unit
  | .unreachable => Unit
  | .drop => code.StackType
  | .select => code.StackType
  | .local_get => U32
  | .local_set => U32
  | .local_tee => U32
  | .global_get => U32
  | .global_set => U32
  | .i32_const => I32
  | .i64_const => I64
  | .f32_const => U32
  | .f64_const => U64

def read (kind : ScalarReaderKind) (st : code.OpIterState) (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) : Result (core.result.Result kind.Parameter error.OpError × code.OpIterState) :=
  match kind with
  | .nop => .ok (.Ok (),st)
  | .unreachable => code.read_unreachable st
  | .drop => code.read_drop st
  | .select => code.read_select st
  | .local_get => code.read_local_get st data ctx
  | .local_set => code.read_local_set st data ctx
  | .local_tee => code.read_local_tee st data ctx
  | .global_get => code.read_global_get st data env
  | .global_set => code.read_global_set st data env
  | .i32_const => code.read_i32_const st data
  | .i64_const => code.read_i64_const st data
  | .f32_const => code.read_f32_const st data
  | .f64_const => code.read_f64_const st data

def action : (kind : ScalarReaderKind) → kind.Parameter → Action
  | .nop => fun _ => .nop
  | .unreachable => fun _ => .unreachable
  | .drop => .drop
  | .select => .select
  | .local_get => .local_get
  | .local_set => .local_set
  | .local_tee => .local_tee
  | .global_get => .global_get
  | .global_set => .global_set
  | .i32_const => .i32_const
  | .i64_const => .i64_const
  | .f32_const => .f32_const
  | .f64_const => .f64_const

/-- Each inventory entry is checked against actual extracted source dispatch. -/
theorem dispatch {V : Type} (kind : ScalarReaderKind) (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (before : V) :
    code.step visitor st data env ctx kind.opcode before =
      CoreVisitor.run (kind.read st data env ctx)
        (fun log state value => invoke visitor log (.op state (kind.action value))) before := by
  cases kind
  · exact dispatch_nop visitor st data env ctx before
  · exact dispatch_unreachable visitor st data env ctx before
  · exact dispatch_drop visitor st data env ctx before
  · exact dispatch_select visitor st data env ctx before
  · exact dispatch_local_get visitor st data env ctx before
  · exact dispatch_local_set visitor st data env ctx before
  · exact dispatch_local_tee visitor st data env ctx before
  · exact dispatch_global_get visitor st data env ctx before
  · exact dispatch_global_set visitor st data env ctx before
  · exact dispatch_i32_const visitor st data env ctx before
  · exact dispatch_i64_const visitor st data env ctx before
  · exact dispatch_f32_const visitor st data env ctx before
  · exact dispatch_f64_const visitor st data env ctx before

theorem ordinary (kind : ScalarReaderKind) : kind.opcode.val ∉ Wasm2.controlOpcodes := by
  cases kind <;> simp only [opcode,global_simps,Wasm2.controlOpcodes] <;> decide

theorem plain (kind : ScalarReaderKind) : kind.opcode.val ∉ [28,37,38,208,209,210,252,253] := by
  cases kind <;> simp only [opcode,global_simps,Wasm2.controlOpcodes] <;> decide

theorem sign (kind : ScalarReaderKind) : Wasm2.NumericExtensions.signMeaning kind.opcode = none := by
  cases kind <;> simp only [opcode,global_simps,Wasm2.NumericExtensions.signMeaning] <;> decide

theorem misc (kind : ScalarReaderKind) : kind.opcode ≠ code.OP_MISC_PREFIX := by
  cases kind <;> simp only [opcode,global_simps,Wasm2.controlOpcodes] <;> decide

/-- Replay every inventory entry from the actual independent source reader.
The source stack and retained compiler layout determine operand shapes. -/
theorem available {A V : Type} (kind : ScalarReaderKind)
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler out bound) (localsMatch : compiler.function.locals = ctx.locals)
    (capacity : st.vals.val.length < Usize.max)
    (outer segment : List code.StackType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length)
    (monomorphic : compiler.reachable = true → Control.polymorphic st = false)
    (known : compiler.reachable = true → ConcreteStack st.vals.val)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.vals.val))
    (reference : code.step source st data env ctx kind.opcode before = .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx kind.opcode compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  cases kind with
  | nop =>
      exact compiler_reader_nop_available ops bound allocation source before after compiler st out data env ctx
        demand reference
  | unreachable =>
      exact compiler_reader_unreachable_available ops bound allocation source before after compiler st out data env ctx
        demand reference
  | drop =>
      exact compiler_reader_drop_available ops bound allocation source before after compiler st out data env ctx
        demand reference
  | select =>
      exact reached_reader_select_available ops bound allocation source before after compiler st out data env ctx
        demand capacity outer segment values base monomorphic known wholeLayout reference
  | local_get =>
      exact compiler_reader_local_get_available ops bound allocation source before after compiler st out data env ctx
        demand localsMatch capacity wholeLayout reference
  | local_set =>
      exact compiler_reader_local_set_available ops bound allocation source before after compiler st out data env ctx
        demand localsMatch capacity outer segment values base monomorphic known wholeLayout reference
  | local_tee =>
      exact compiler_reader_local_tee_available ops bound allocation source before after compiler st out data env ctx
        demand localsMatch capacity outer segment values base monomorphic known wholeLayout reference
  | global_get =>
      exact compiler_reader_global_get_available ops bound allocation source before after compiler st out data env ctx
        demand reference
  | global_set =>
      exact reached_reader_global_set_available ops bound allocation source before after compiler st out data env ctx
        demand outer segment values base monomorphic known wholeLayout reference
  | i32_const =>
      exact compiler_reader_i32_const_available ops bound allocation source before after compiler st out data env ctx
        demand reference
  | i64_const =>
      exact compiler_reader_i64_const_available ops bound allocation source before after compiler st out data env ctx
        demand reference
  | f32_const =>
      exact compiler_reader_f32_const_available ops bound allocation source before after compiler st out data env ctx
        demand reference
  | f64_const =>
      exact compiler_reader_f64_const_available ops bound allocation source before after compiler st out data env ctx
        demand reference

end ScalarReaderKind
end Itasca.Runtime.Compiler

end

/-! ## StatefulCallbackAcceptance -/

section

/-!
Stateful reader acceptance and its callback-action lift. StatefulReaderPost.available connects the source postcondition to actual callback replay.
-/

/-! ## Stateful Reader Acceptance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Independent Wasm 2 source-reader typing supplies the complete
stateful signature and live operands. Dead paths only observe the source stack.
This covers references, table operations, and memory/bulk metadata callbacks. -/
theorem StatefulReaderPost.available {data env locals index st} {p : Wasm2.Pending data env locals index st}
    {out : code.OpIterState} {op : SourceMachine.Stateful.Instruction} (post : StatefulReaderPost p out op)
    {A : Type} (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (demand : CallbackDemand compiler out bound)
    (C : context) (matched : EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (pairs : compiler.function.indirect.length ≤ compiler.function.code.length) (a b : U32) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler out (statefulOpcode op) a b 0#u128 ⦃ result =>
      result.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget result.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨_,_,typesPost⟩ := post
    obtain ⟨front,input,output,signature,beforeTypes,_⟩ := typesPost C matched (known live) (monomorphic live)
    have layout := wholeLayout live
    rw [beforeTypes] at layout
    have pc := demand.pc
    have capacity := demand.codeCapacity
    have reserve := demand.codeReserve
    simp only [alloc.vec.Vec.length] at pairs pc capacity reserve
    exact compiler_stateful_available ops bound available compiler out demand C front input output op signature a b
      (fun _ => layout)
      (fun _ => by change compiler.function.indirect.val.length ≤ U32.max; omega)
      (fun _ => by change compiler.function.indirect.val.length < Usize.max; omega)
      (fun _ => by change compiler.function.indirect.val.length+1 ≤ bound; omega)
  · apply WP.spec_mono (compiler_dead_op_available ops bound available compiler out (statefulOpcode op) a b
      0#u128 live demand.operands demand.slots)
    intro result held
    rw [held.2]
    exact ⟨held.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Runtime.Compiler

end

/-! ## Stateful Callback Acceptance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Named source event for each actual stateful visitor hook. -/
def statefulAction (op : SourceMachine.Stateful.Instruction) (a b : U32) : Action :=
  match op with
  | .refNull .FUNCREF => .ref_null .FuncRef
  | .refNull .EXTERNREF => .ref_null .ExternRef
  | .refFunc _ => .ref_func a
  | .refIsNull => .ref_is_null
  | .tableGet _ => .table_get a
  | .tableSet _ => .table_set a
  | .tableSize _ => .table_size a
  | .tableGrow _ => .table_grow a
  | .tableFill _ => .table_fill a
  | .tableCopy .. => .table_copy a b
  | .tableInit .. => .table_init a b
  | .elemDrop _ => .elem_drop a
  | .memorySize => .memory_size
  | .memoryGrow => .memory_grow
  | .memoryFill => .memory_fill
  | .memoryCopy => .memory_copy
  | .memoryInit _ => .memory_init a
  | .dataDrop _ => .data_drop a

theorem stateful_callback_invoke {V : Type} (visitor : code.OpVisitor V) (before : V)
    (state : code.OpIterState) (op : SourceMachine.Stateful.Instruction) (a b : U32) :
    statefulCallback visitor before state op a b = invoke visitor before (.op state (statefulAction op a b)) := by
  cases op <;> try rfl
  rename_i ty
  cases ty <;> rfl

/-- Source-reader typing and bounded lowering establish acceptance of the
actual stateful hook, with the checked compiler argument order. -/
theorem StatefulReaderPost.callback_available {data env locals index st} {p : Wasm2.Pending data env locals index st}
    {out : code.OpIterState} {op : SourceMachine.Stateful.Instruction} (post : StatefulReaderPost p out op)
    {A : Type} (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (demand : CallbackDemand compiler out bound)
    (C : context) (matched : EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (pairs : compiler.function.indirect.length ≤ compiler.function.code.length)
    (a b : U32) (arguments : StatefulArguments op a b) :
    statefulCallback (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler out op a b
      ⦃ result => result.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget result.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [stateful_callback_lower ops compiler out op a b arguments]
  exact post.available ops bound allocation compiler demand C matched known monomorphic wholeLayout pairs a b

end Itasca.Runtime.Compiler

end

end

/-! ## RecordedAcceptance -/

section

/-!
Equal successful recorder transitions name the same source event. This uses the independently defined recorder; it assumes no target behavior.

Main declarations: `recorder_invocation_unique` and `recorded_reader_available`. A direct consumer is `Compiler.Body.Reader.Acceptance.SourceBoundTypedSelectAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Equal successful recorder transitions name the same source event. This
uses the independently defined recorder; it assumes no target behavior. -/
theorem recorder_invocation_unique (before after : List Observation) (first second : Event)
    (left : invoke recorder before first = .ok (.Ok (),after))
    (right : invoke recorder before second = .ok (.Ok (),after)) : first = second := by
  have leftLog := recorder_records before first (.Ok ()) after left
  have rightLog := recorder_records before second (.Ok ()) after right
  dsimp only [id] at leftLog rightLog
  have same := List.append_cancel_left (leftLog.symm.trans rightLog)
  exact congrArg Observation.event (List.cons.inj same).1

/-- Replay a parsed single-event reader using the actual event established by
independent source analysis. Event uniqueness avoids assuming injective
callback behavior of arbitrary native visitors. -/
theorem recorded_reader_available {R W : Type}
    (read : Result (core.result.Result R error.OpError × code.OpIterState))
    (action : R → Action) (target : code.OpVisitor W) (compiler : W)
    (before after : List Observation) (out : code.OpIterState) (knownAction : Action) (post : W → Prop)
    (reference : CoreVisitor.run read (fun log state value => invoke recorder log (.op state (action value))) before =
      .ok (.Ok (),out,after))
    (known : invoke recorder before (.op out knownAction) = .ok (.Ok (),after))
    (acceptance : invoke target compiler (.op out knownAction) ⦃ result => result.1 = .Ok () ∧ post result.2 ⦄) :
    CoreVisitor.run read (fun current state value => invoke target current (.op state (action value))) compiler
      ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧ post result.2.2 ⦄ := by
  refine CoreVisitor.run.accepted_lift_on read _ _ before after compiler out post reference ?_
  intro value _ called
  have same := recorder_invocation_unique before after (.op out (action value)) (.op out knownAction) called known
  rw [same]
  exact acceptance

end Itasca.Runtime.Compiler

end
