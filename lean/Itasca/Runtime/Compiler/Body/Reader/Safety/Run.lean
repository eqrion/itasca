import Itasca.Runtime.Compiler.Local.Relations.Select.SelectSafety
import Itasca.Visitor.Basic

/-!
Only a reader's actual successful result needs a returning compiler hook. Parser and callback rejections are included in the normal-return conclusion.

Main declarations: `reader_run_reached` and `compiler_select_raw_total`. A direct consumer is `Compiler.Body.Reader.Calls.Safety`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Only a reader's actual successful result needs a returning compiler hook.
Parser and callback rejections are included in the normal-return conclusion. -/
theorem reader_run_reached {T V : Type}
    (read : Result (core.result.Result T error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → T → Result (core.result.Result Unit error.VisitError × V))
    (visitor : V) (post : code.OpIterState → V → Prop)
    (reader : read ⦃ _ => True ⦄)
    (callback : ∀ state value, read = .ok (.Ok value,state) →
      hook visitor state value ⦃ out => out.1 = .Ok () → post state out.2 ⦄) :
    CoreVisitor.run read hook visitor ⦃ out => out.1 = .Ok () → post out.2.1 out.2.2 ⦄ := by
  obtain ⟨⟨result,state⟩,readEq,_⟩ := WP.spec_imp_exists reader
  cases result with
  | Err error => simp [CoreVisitor.run,readEq,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok value =>
    obtain ⟨⟨result,after⟩,called,ready⟩ := WP.spec_imp_exists (callback state value readEq)
    cases result with
    | Err error => simp [CoreVisitor.run,readEq,called,code.visit,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok unitValue =>
      cases unitValue
      simpa [CoreVisitor.run,readEq,called,code.visit,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,WP.spec_ok] using ready rfl

/-- SELECT can reject an undersized raw operand stack normally; only ordered
observed offsets, including bottom-valued stacks, are needed for subtraction. -/
theorem compiler_select_raw_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) (values : List code.StackType) (typed : Bool)
    (observed : ObservedStack compiler values)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state
      (if typed then 28#u16 else 27#u16) 0#u32 0#u32 0#u128 ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  by_cases enough : 3 ≤ values.length
  · exact compiler_select_total ops law compiler state values typed observed (fun _ => enough)
      codeFits sourceFits coordinateFits
  · by_cases live : compiler.reachable = true
    · have lower : runtime.compiler.lower.FunctionCompiler.op ops compiler state
          (if typed then 28#u16 else 27#u16) 0#u32 0#u32 0#u128 = selectLowering ops compiler state := by
        cases typed <;> unfold runtime.compiler.lower.FunctionCompiler.op <;> rw [if_pos live] <;> rfl
      have bound : Slice.len compiler.before.deref < 3#usize := by
        have len := observed.length
        simp only [alloc.vec.Vec.deref,Slice.len,Slice.length,Slice.from_val]
        scalar_tac
      have missing : runtime.compiler.FunctionCompiler.operand ops compiler 3#usize =
          .ok (.Err error.VisitError.OutOfMemory) := by
        simp [runtime.compiler.FunctionCompiler.operand,runtime.compiler.operand_at,bound]
      rw [lower]
      simp [selectLowering,missing,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    · unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_neg live]
      exact compiler_observe_stack ops law compiler state
end Itasca.Runtime.Compiler
