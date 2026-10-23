import Exec.Code.Local.Capacity.ReaderAcceptance
import Itasca.Visitor.ReachedTableLabels
import Exec.Code.Local.Capacity.BranchLabelAvailability
import Exec.Code.Local.Relations.Table.BranchTableCallback

namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Collected labels change only scratch storage and budget counters. The
resource allowance is indexed by source labels, independent of emitted code. -/
def LabelCollectionPrefix {A : Type} (initial current : runtime.compiler.FunctionCompiler A)
    (count : Nat) : Prop :=
  ∃ budget depths, current = {initial with budget,table_depths := depths} ∧
    depths.length = initial.table_depths.length+count ∧
    CompilationBudgetEffect initial.budget budget (fun counter => if counter = .branches then count else 0)

theorem LabelCollectionPrefix.initial {A : Type} (compiler : runtime.compiler.FunctionCompiler A) :
    LabelCollectionPrefix compiler compiler 0 := by
  exact ⟨compiler.budget,compiler.table_depths,rfl,by omega,by
    simpa using CompilationBudgetEffect.refl compiler.budget⟩

/-- The actual next label accepts from the unconsumed portion of independently
bounded scratch and branch demand. All other compiler fields are retained. -/
theorem LabelCollectionPrefix.collect_available {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (initial compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState) (depth : U32)
    (count total : Nat) (held : LabelCollectionPrefix initial compiler count) (remaining : count < total)
    (branches : initial.budget.branches.val+total ≤ initial.budget.limits.max_branch_table_entries.val)
    (capacity : initial.table_depths.length+total ≤ Usize.max)
    (reserve : initial.table_depths.length+total ≤ bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label ops compiler state depth ⦃ out =>
      out.1 = .Ok () ∧ LabelCollectionPrefix initial out.2 (count+1) ⦄ := by
  obtain ⟨budget,depths,frame,length,effect⟩ := held
  have used := (effect.counts .branches).2
  have limits := effect.limits
  have room : compiler.budget.branches.val < compiler.budget.limits.max_branch_table_entries.val := by
    rw [frame]
    simp only [ChargeCounter.used,ite_true] at used
    simp only
    rw [limits]
    omega
  have fits : compiler.table_depths.length < Usize.max := by rw [frame]; simp only; omega
  have request : compiler.table_depths.length+1 ≤ bound := by rw [frame]; simp only; omega
  obtain ⟨⟨reply,after⟩,called,accepted,growth,appended⟩ := WP.spec_imp_exists
    (compiler_branch_label_available ops bound available compiler state depth room fits request)
  dsimp only at accepted growth appended
  subst reply
  obtain ⟨nextBudget,nextDepths,nextFrame,nextValues⟩ := compiler_table_label_success ops law compiler after state depth called
  have counts : nextDepths.length = initial.table_depths.length+(count+1) := by
    have lengths := congrArg List.length nextValues
    simp only [List.length_append,List.length_singleton] at lengths
    change nextDepths.length = compiler.table_depths.length+1 at lengths
    rw [frame] at lengths
    simp only at lengths
    omega
  have nextEffect : CompilationBudgetEffect initial.budget nextBudget
      (fun counter => if counter = .branches then count+1 else 0) := by
    rw [nextFrame] at growth
    rw [frame] at growth
    exact (effect.trans growth).weaken (by intro counter; cases counter <;> simp)
  apply WP.exists_imp_spec
  refine ⟨(.Ok (),after),called,rfl,nextBudget,nextDepths,?_,counts,nextEffect⟩
  rw [nextFrame,frame]

end Exec.Code
