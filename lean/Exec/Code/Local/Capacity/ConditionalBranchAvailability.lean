import Exec.Code.Local.Capacity.ConditionalElidedAvailability
import Exec.Code.Local.Capacity.ConditionalTransferAvailability
import Exec.Code.Local.Capacity.ObserveBudgetAvailability
import Exec.Code.Local.Callbacks.Control.CompilerBranchMetadata

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Conditional branches accept at every label depth and kind with at most
three instructions. Widths and the condition coordinate are source-layout
premises; the resume PC is constructed by the actual checked lowering. -/
theorem compiler_conditional_branch_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 3)
    (frame : runtime.compiler.Frame) (index : Usize) (depth condition : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (widthFits : (match frame.kind with | .Loop => frame.params | _ => frame.results).val + 1 ≤ compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (fixupsCapacity : frame.fixups.length < Usize.max)
    (fixupsReserve : frame.fixups.length + 1 ≤ bound) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 3 else 0) ⦄ := by
  by_cases loopEntry : frame.kind = .Loop
  · have enough : frame.params.val + 1 ≤ compiler.height.val := by simpa only [loopEntry] using widthFits
    let source : U32 := UScalar.ofNatCore (compiler.height.val-(frame.params.val+1)) (by scalar_tac)
    have sourcePosition : source.val + frame.params.val + 1 = compiler.height.val := by
      change compiler.height.val-(frame.params.val+1)+frame.params.val+1 = compiler.height.val
      omega
    by_cases elided : frame.params = 0#u32 ∨ source = frame.height
    · apply WP.spec_mono (branch_if_elided_loop_available ops bound available compiler state (capacity.mono (by decide))
        frame index depth source condition lookup position loopEntry elided sourcePosition conditionAt)
      intro out post
      exact ⟨post.1,post.2.weaken (by intro counter; cases counter <;> simp)⟩
    · exact branch_if_transfer_loop_available ops law bound available compiler state capacity frame index depth source condition
        lookup position loopEntry (by intro zero; exact elided (.inl zero))
        (by intro same; exact elided (.inr same)) sourcePosition conditionAt
  · have enough : frame.results.val + 1 ≤ compiler.height.val := by
      cases kindEq : frame.kind
      all_goals first | exact False.elim (loopEntry kindEq) | simpa only [kindEq] using widthFits
    let source : U32 := UScalar.ofNatCore (compiler.height.val-(frame.results.val+1)) (by scalar_tac)
    have sourcePosition : source.val + frame.results.val + 1 = compiler.height.val := by
      change compiler.height.val-(frame.results.val+1)+frame.results.val+1 = compiler.height.val
      omega
    by_cases elided : frame.results = 0#u32 ∨ source = frame.height
    · apply WP.spec_mono (branch_if_elided_forward_available ops bound available compiler state (capacity.mono (by decide))
        frame index depth source condition lookup position loopEntry elided sourcePosition conditionAt fixupsCapacity fixupsReserve)
      intro out post
      exact ⟨post.1,post.2.weaken (by intro counter; cases counter <;> simp)⟩
    · exact branch_if_transfer_forward_available ops law bound available compiler state capacity frame index depth source condition
        lookup position loopEntry (by intro zero; exact elided (.inl zero))
        (by intro same; exact elided (.inr same)) sourcePosition conditionAt fixupsCapacity fixupsReserve

/-- The actual br_if callback also accepts unreachable paths, which only
observe the validator stack and retain the compilation budget. -/
theorem compiler_on_br_if_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 3)
    (frame : runtime.compiler.Frame) (index : Usize) (depth condition : U32) (resultType : Itasca.signature.ResultType)
    (lookup : compiler.reachable = true → compiler.frames.val[index.val]? = some frame)
    (position : compiler.reachable = true → index.val + depth.val + 1 = compiler.frames.val.length)
    (widthFits : compiler.reachable = true →
      (match frame.kind with | .Loop => frame.params | _ => frame.results).val + 1 ≤ compiler.height.val)
    (conditionAt : compiler.reachable = true → compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (fixupsCapacity : frame.fixups.length < Usize.max)
    (fixupsReserve : frame.fixups.length + 1 ≤ bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops compiler state depth resultType ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 3 else 0) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
  by_cases live : compiler.reachable = true
  · rw [if_pos live]
    obtain ⟨⟨status,branched⟩,actual,accepted,effect⟩ := WP.spec_imp_exists
      (compiler_conditional_branch_available ops law bound available compiler state capacity frame index depth condition
        (lookup live) (position live) (widthFits live) (conditionAt live) fixupsCapacity fixupsReserve)
    dsimp only at accepted effect
    subst status
    rw [actual]
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have stable := compiler_branch_stable_result ops law compiler branched depth 1#u32 true (.Ok ()) actual
    have localsSame := stable.fields.2.2.2.2.2.2.1
    have slotsFit : branched.function.local_slots.val + 2*state.vals.length ≤ U32.max := by
      rw [localsSame]; exact capacity.slots
    apply WP.spec_mono (compiler_observe_available_budget ops bound available branched state capacity.operands slotsFit)
    intro out post
    rw [post.2]
    exact ⟨post.1,effect⟩
  · rw [if_neg live]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state capacity.operands capacity.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Exec.Code
