import Exec.Code.Local.Relations.Table.BranchTableTarget
import Exec.Code.Local.Relations.Table.BranchTableTrace
import Exec.Code.Local.Relations.Table.TableDepths
namespace Exec.Code
open Aeneas Aeneas.Std

/-- Syntax-only production certificate for the ordered branch fragments. Each
entry records its actual dispatch PC and exact relocation or loop backedge. -/
inductive TableTargetsBuilt {A : Type} : runtime.compiler.FunctionCompiler A →
    runtime.compiler.FunctionCompiler A → List U32 → List U32 → Prop where
  | nil (compiler) : TableTargetsBuilt compiler compiler [] []
  | cons {before middle after depths targets} (depth target : U32)
      (targetPC : target.val = before.function.code.val.length)
      (appended : middle.function.jump_tables.val = before.function.jump_tables.val ++ [target])
      (height : middle.height = before.height)
      (depthsSame : middle.table_depths = before.table_depths)
      (fragment : TableTargetCode before middle depth)
      (rest : TableTargetsBuilt middle after depths targets) :
      TableTargetsBuilt before after (depth :: depths) (target :: targets)

theorem TableTargetsBuilt.tables {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {depths targets : List U32} (built : TableTargetsBuilt before after depths targets) :
    after.function.jump_tables.val = before.function.jump_tables.val ++ targets := by
  induction built with
  | nil => simp
  | cons depth target pc appended height same fragment rest ih =>
    rw [ih,appended]
    simp

theorem TableTargetsBuilt.length {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {depths targets : List U32} (built : TableTargetsBuilt before after depths targets) :
    targets.length = depths.length := by
  induction built with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ ih => simpa using ih

theorem TableTargetsBuilt.height {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {depths targets : List U32} (built : TableTargetsBuilt before after depths targets) :
    after.height = before.height := by
  induction built with
  | nil => rfl
  | cons _ _ _ _ height _ _ _ ih => exact ih.trans height

/-- Eliminate every actual call in the accepted finite loop into its exact
ordered code/table effect. The result has no execution-correctness premise. -/
theorem TableBranchRun.built {A : Type} {ops : runtime.platform.Alloc A}
    (law : Platform.AllocCorrect ops) {before after : runtime.compiler.FunctionCompiler A}
    {index : Nat} (run : TableBranchRun ops before index after) :
    ∃ targets, TableTargetsBuilt before after (before.table_depths.val.drop index) targets := by
  induction run with
  | done compiler index finished =>
    exact ⟨[], by simpa only [List.drop_eq_nil_of_le finished] using TableTargetsBuilt.nil compiler⟩
  | @cons before middle after index inside called rest ih =>
    let depth := before.table_depths.val[index.val]
    have lookup : before.table_depths.val[index.val]? = some depth := by simp [depth,inside]
    obtain ⟨target,pc,appended,height,fragment⟩ :=
      compiler_table_target_code ops law before middle index depth lookup called
    have same := compiler_table_branch_depths ops before middle index (.Ok ()) called
    obtain ⟨targets,built⟩ := ih
    rw [same] at built
    refine ⟨target::targets, ?_⟩
    have split : before.table_depths.val.drop index.val =
        depth :: before.table_depths.val.drop (index.val+1) := by
      exact List.drop_eq_getElem_cons inside
    rw [split]
    exact .cons depth target pc appended height same fragment built
theorem TableTargetCode.code_prefix {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depth : U32}
    (effect : TableTargetCode before after depth) :
    ∃ fragment, after.function.code.val = before.function.code.val ++ fragment ∧ 1 ≤ fragment.length := by
  cases effect with
  | loop index frame source lookup position kind operands code frames =>
    exact ⟨_,code,by simp only [branchInstructions]; split <;> simp⟩
  | forward index frame source fixups site lookup position kind operands code frames appended sitePosition =>
    exact ⟨_,code,by simp only [branchInstructions]; split <;> simp⟩

theorem TableTargetsBuilt.code_prefix {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {depths targets : List U32} (built : TableTargetsBuilt before after depths targets) :
    ∃ fragment, after.function.code.val = before.function.code.val ++ fragment ∧ depths.length ≤ fragment.length := by
  induction built with
  | nil => exact ⟨[],by simp,by simp⟩
  | cons depth target pc appended height same effect rest ih =>
    obtain ⟨first,firstCode,firstLength⟩ := effect.code_prefix
    obtain ⟨remaining,restCode,restLength⟩ := ih
    exact ⟨first++remaining,by rw [restCode,firstCode,List.append_assoc],by simp only [List.length_append,List.length_cons]; omega⟩
end Exec.Code
