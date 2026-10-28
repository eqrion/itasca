import Itasca.Runtime.Code.Local.Capacity.BranchLoopAvailability
import Itasca.Runtime.Code.Local.Capacity.BranchForwardAvailability
import Itasca.Runtime.Code.Local.Capacity.ObserveBudgetAvailability
import Itasca.Runtime.Code.Local.Callbacks.Control.CompilerBranchMetadata

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Raw unconditional branching accepts for every label kind and depth. The
source width bound excludes arithmetic rejection; reserves pay for fixups. -/
theorem compiler_unconditional_branch_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 2)
    (frame : runtime.compiler.Frame) (index : Usize) (depth skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (widthFits : (match frame.kind with | .Loop => frame.params | _ => frame.results).val + skip.val ≤ compiler.height.val)
    (fixupsCapacity : frame.fixups.length < Usize.max)
    (fixupsReserve : frame.fixups.length + 1 ≤ bound) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 2 else 0) ⦄ := by
  by_cases loopEntry : frame.kind = .Loop
  · exact compiler_branch_loop_available ops law bound available compiler state capacity frame index depth skip
      lookup position loopEntry (by simpa only [loopEntry] using widthFits)
  · have resultsFit : frame.results.val + skip.val ≤ compiler.height.val := by
      cases kindEq : frame.kind
      all_goals first | exact False.elim (loopEntry kindEq) | simpa only [kindEq] using widthFits
    exact compiler_branch_forward_available ops law bound available compiler state capacity frame index depth skip
      lookup position loopEntry resultsFit fixupsCapacity fixupsReserve

/-- The actual br callback composes available raw branching and dead-stack
observation. Accepted primitive equations are constructed inside this proof. -/
theorem compiler_on_br_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 2)
    (frame : runtime.compiler.Frame) (index : Usize) (depth : U32) (resultType : Itasca.signature.ResultType)
    (lookup : compiler.reachable = true → compiler.frames.val[index.val]? = some frame)
    (position : compiler.reachable = true → index.val + depth.val + 1 = compiler.frames.val.length)
    (widthFits : compiler.reachable = true →
      (match frame.kind with | .Loop => frame.params | _ => frame.results).val ≤ compiler.height.val)
    (fixupsCapacity : frame.fixups.length < Usize.max)
    (fixupsReserve : frame.fixups.length + 1 ≤ bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops compiler state depth resultType ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 2 else 0) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
  by_cases live : compiler.reachable = true
  · rw [if_pos live]
    obtain ⟨⟨status,branched⟩,actual,accepted,effect⟩ := WP.spec_imp_exists
      (compiler_unconditional_branch_available ops law bound available compiler state capacity frame index depth 0#u32
        (lookup live) (position live) (widthFits live) fixupsCapacity fixupsReserve)
    dsimp only at accepted effect
    subst status
    rw [actual]
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    change runtime.compiler.FunctionCompiler.observe ops {branched with reachable := false} state ⦃ out => _ ⦄
    have stable := compiler_branch_stable_result ops law compiler branched depth 0#u32 false (.Ok ()) actual
    have localsSame := stable.fields.2.2.2.2.2.2.1
    have slotsFit : branched.function.local_slots.val + 2*state.vals.length ≤ U32.max := by
      rw [localsSame]; exact capacity.slots
    apply WP.spec_mono (compiler_observe_available_budget ops bound available {branched with reachable := false}
      state capacity.operands slotsFit)
    intro out post
    rw [post.2]
    exact ⟨post.1,effect⟩
  · rw [if_neg live]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state capacity.operands capacity.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Runtime.Code
