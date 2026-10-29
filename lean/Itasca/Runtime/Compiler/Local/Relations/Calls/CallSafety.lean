import Itasca.Runtime.Compiler.Local.Relations.Operations.PairSafety
import Itasca.Runtime.Compiler.Local.Lowering.Calls.LoweringCall
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallLowering

/-! Call callback safety includes checked arithmetic and operand rejections. -/
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

@[step] theorem compiler_call_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (index : U32)
    (indexBound : index.val < compiler.func_param_slots.val.length)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 16#u16 index 0#u32 0#u128 ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  by_cases reachable : compiler.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops compiler state 16#u16 index 0#u32 0#u128 = (do
        let i ← lift (UScalar.cast .Usize index)
        let slots ← Slice.index_usize compiler.func_param_slots i
        let o ← lift (U32.checked_sub compiler.height slots)
        let r ← core.option.Option.ok_or o Itasca.error.VisitError.OutOfMemory
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val =>
          runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state (.Call index val)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame Itasca.error.VisitError) residual
          Result.ok (r1, compiler)) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reachable]
      rfl
    rw [run]
    step as ⟨i, hi⟩
    have bound : i.val < compiler.func_param_slots.length := by scalar_tac
    step as ⟨slots, hslots⟩
    cases difference : U32.checked_sub compiler.height slots with
    | none => simp [lift,difference,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | some base =>
      simp only [difference,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,lift,bind_ok]
      exact finish_op_observed ops law compiler state _ codeFits sourceFits coordinateFits
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg reachable]
    exact compiler_observe_stack ops law compiler state

@[step] theorem compiler_indirect_call_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (typeIndex tableIndex : U32)
    (indexBound : typeIndex.val < compiler.signatures.val.length)
    (pairFits : compiler.function.indirect.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 17#u16 typeIndex tableIndex 0#u128 ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  by_cases reachable : compiler.reachable = true
  · rw [lower_indirect_call_dispatch ops compiler state typeIndex tableIndex reachable]
    unfold indirectCallLowering
    step as ⟨i, hi⟩
    have bound : i.val < compiler.signatures.length := by scalar_tac
    step as ⟨signature, hsignature⟩
    cases added : U32.checked_add signature.param_slots 1#u32 with
    | none => simp [lift,added,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | some total =>
      simp only [added,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,lift,bind_ok]
      cases subtracted : U32.checked_sub compiler.height total with
      | none => simp [lift,subtracted,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | some base =>
        simp only [subtracted,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,lift,bind_ok]
        step with compiler_pair_total ops law compiler tableIndex typeIndex pairFits
          as ⟨answer,paired,budget,pairs,effect⟩
        subst paired
        cases answer with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok entry =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
          step with compiler_operand_total ops _ 1#usize as ⟨answer,_⟩
          cases answer with
          | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok selector =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
            exact finish_op_observed ops law _ state _ codeFits sourceFits coordinateFits
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg reachable]
    exact compiler_observe_stack ops law compiler state

@[step] theorem compiler_on_call_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (index : U32)
    (indexBound : index.val < compiler.func_param_slots.val.length)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_call compiler state index ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ :=
  compiler_call_total ops law compiler state index indexBound codeFits sourceFits coordinateFits

@[step] theorem compiler_on_call_indirect_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (typeIndex tableIndex : U32)
    (indexBound : typeIndex.val < compiler.signatures.val.length)
    (pairFits : compiler.function.indirect.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_call_indirect compiler state typeIndex tableIndex ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ :=
  compiler_indirect_call_total ops law compiler state typeIndex tableIndex indexBound pairFits codeFits sourceFits coordinateFits

end Itasca.Runtime.Code
