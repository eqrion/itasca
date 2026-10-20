import Exec.Code.Local.Capacity.TableLowerAvailability
import Exec.Code.Local.Capacity.BranchLabelAvailability
import Exec.Code.Local.Relations.Table.BranchTableMetadata

namespace Exec.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Actual br_table accepts all collected labels plus the fallback. The
source bounds cover every target; temporary storage and both charged resources
have independent numeric demand. Dead paths still charge the fallback label. -/
theorem compiler_on_br_table_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (fallback : U32) (resultType : Itasca.signature.ResultType) (selector : U32)
    (capacity : CallbackCapacity compiler state bound (2*(compiler.table_depths.val.length+1)+1))
    (branchRoom : compiler.budget.branches.val < compiler.budget.limits.max_branch_table_entries.val)
    (scratchCapacity : compiler.table_depths.length < Usize.max)
    (scratchReserve : compiler.table_depths.length+1 ≤ bound)
    (depthCount : compiler.table_depths.val.length+1 ≤ U32.max)
    (aligned : compiler.reachable = true → SourceAligned compiler)
    (depthsValid : compiler.reachable = true → ∀ depth ∈ compiler.table_depths.val ++ [fallback],
      depth.val < compiler.frames.val.length)
    (widths : compiler.reachable = true → ∀ depth ∈ compiler.table_depths.val ++ [fallback],
      ∀ (index : Usize) (frame : runtime.compiler.Frame), compiler.frames.val[index.val]? = some frame →
        index.val+depth.val+1 = compiler.frames.val.length → (frameBranchWidth frame).val+1 ≤ compiler.height.val)
    (fixups : compiler.reachable = true → FixupBudget compiler.frames.val compiler.function.code.val.length)
    (tables : compiler.reachable = true → compiler.function.jump_tables.val.length ≤ compiler.function.code.val.length)
    (selectorAt : compiler.reachable = true → compiler.before.val[compiler.before.val.length-1]? = some selector) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table ops compiler state fallback resultType ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => match counter with
          | .instructions => 2*(compiler.table_depths.val.length+1)+1 | .branches => 1 | _ => 0) ⦄ := by
  obtain ⟨⟨status,labeled⟩,labelCalled,accepted,labelEffect,_⟩ := WP.spec_imp_exists
    (compiler_branch_label_available ops bound available compiler state fallback branchRoom scratchCapacity scratchReserve)
  dsimp only at accepted labelEffect
  subst status
  obtain ⟨budget,depths,frame,depthsEq⟩ := compiler_table_label_success ops law compiler labeled state fallback labelCalled
  subst labeled
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
  rw [labelCalled]
  simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  have lengthEq : depths.val.length = compiler.table_depths.val.length+1 := by simp [depthsEq]
  have limitsSame : budget.limits = compiler.budget.limits := labelEffect.limits
  have instructionsSame : budget.instructions = compiler.budget.instructions := labelEffect.uncharged .instructions (by decide)
  let staged := {compiler with budget,table_depths := depths}
  by_cases live : compiler.reachable = true
  · rw [if_pos live]
    have stagedCapacity : CallbackCapacity staged state bound (2*depths.val.length+1) := by
      refine ⟨?_,?_,?_,?_,?_,capacity.coordinate,?_,capacity.operands,capacity.slots⟩
      · simpa only [staged,lengthEq] using capacity.pc
      · simpa only [staged,lengthEq] using capacity.codeCapacity
      · simpa only [staged,lengthEq] using capacity.sourceCapacity
      · simpa only [staged,lengthEq] using capacity.codeReserve
      · simpa only [staged,lengthEq] using capacity.sourceReserve
      · change budget.instructions.val+(2*depths.val.length+1) ≤ budget.limits.max_instructions.val
        rw [instructionsSame,limitsSame,lengthEq]
        exact capacity.instructions
    have stagedDepths : ∀ depth ∈ staged.table_depths.val, depth.val < staged.frames.val.length := by
      simpa only [staged,depthsEq] using depthsValid live
    have stagedWidths : TableWidthsFit staged := by
      simpa only [TableWidthsFit,staged,depthsEq] using widths live
    obtain ⟨⟨status,lowered⟩,lowerCalled,accepted,lowerEffect⟩ := WP.spec_imp_exists
      (compiler_lower_table_available ops law bound available staged state stagedCapacity (aligned live)
        stagedDepths stagedWidths (fixups live) (tables live)
        (by change depths.val.length ≤ U32.max; omega) selector (selectorAt live))
    dsimp only at accepted lowerEffect
    subst status
    rw [lowerCalled]
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with compiler_clear_table_depths lowered.table_depths as ⟨cleared,_⟩
    have fixed := (compiler_lower_table_fixed ops law staged lowered lowerCalled).stable.fields
    have localsSame := fixed.2.2.2.2.2.2.1
    have slotsFit : lowered.function.local_slots.val+2*state.vals.length ≤ U32.max := by
      rw [localsSame]; exact capacity.slots
    apply WP.spec_mono (compiler_observe_available_budget ops bound available
      {lowered with reachable := false,table_depths := cleared} state capacity.operands slotsFit)
    intro out post
    rw [post.2]
    exact ⟨post.1,(labelEffect.trans lowerEffect).weaken
      (by intro counter; cases counter <;> simp [staged,lengthEq])⟩
  · rw [if_neg live]
    step with compiler_clear_table_depths depths as ⟨cleared,_⟩
    let observed := {compiler with budget,table_depths := cleared}
    apply WP.spec_mono (compiler_observe_available_budget ops bound available observed state capacity.operands capacity.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,labelEffect.weaken (by intro counter; cases counter <;> simp)⟩

end Exec.Code
