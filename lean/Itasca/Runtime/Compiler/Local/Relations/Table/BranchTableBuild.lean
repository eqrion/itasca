import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchContracts
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Copy
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Emit
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Frame
import Itasca.Runtime.Compiler.Local.Relations.Layout.ValueRegions
import Itasca.Runtime.Compiler.Local.Relations.Table.ControlTablePreservation
import Itasca.Runtime.Compiler.Local.Lowering.Control.TableBranchContracts
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableTrace
import Itasca.Runtime.Compiler.Local.Relations.Table.TableDepths

/-!
Construction of br_table targets with their emitted heights and table correspondence. TableTargetsBuilt records the target-by-target invariant consumed by loop proofs.
-/

/-! ## Branch Table Height -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096




theorem compiler_branch_height_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status, after)) :
    after.height = before.height := by
  have frame := (runtime.compiler.control.FunctionCompiler.branch.inv ops before after depth skip conditional status accepted).frame
  rw [frame]

end Itasca.Runtime.Compiler

end

/-! ## Branch Table Target -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Exact syntactic effect of a table arm. Forward destinations retain their
new relocation site; loop arms retain the already resolved backedge. -/
inductive TableTargetCode {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (depth : U32) : Prop where
  | loop (index : Usize) (frame : runtime.compiler.Frame) (source : U32)
      (lookup : before.frames.val[index.val]? = some frame)
      (position : index.val + depth.val + 1 = before.frames.val.length)
      (kind : frame.kind = .Loop)
      (operands : source.val + frame.params.val + 1 = before.height.val)
      (code : after.function.code.val = before.function.code.val ++
        branchInstructions frame.height source frame.params frame.start_pc)
      (frames : after.frames = before.frames) : TableTargetCode before after depth
  | forward (index : Usize) (frame : runtime.compiler.Frame) (source : U32)
      (fixups : alloc.vec.Vec Usize) (site : Usize)
      (lookup : before.frames.val[index.val]? = some frame)
      (position : index.val + depth.val + 1 = before.frames.val.length)
      (kind : frame.kind ≠ .Loop)
      (operands : source.val + frame.results.val + 1 = before.height.val)
      (code : after.function.code.val = before.function.code.val ++
        branchInstructions frame.height source frame.results core.num.U32.MAX)
      (frames : after.frames.val = before.frames.val.set index.val {frame with end_reachable := true,fixups})
      (appended : fixups.val = frame.fixups.val ++ [site])
      (sitePosition : site.val = before.function.code.val.length +
        (if frame.results = 0#u32 ∨ source = frame.height then 0 else 1)) :
      TableTargetCode before after depth

/-- Successful actual arm lowering establishes the complete exact code/fixup
certificate, including source operand safety from its accepted checked arithmetic. -/
theorem compiler_table_target_code {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32) (lookup : before.table_depths.val[index.val]? = some depth)
    (accepted : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (),after)) :
    ∃ target,
      target.val = before.function.code.val.length ∧
      after.function.jump_tables.val = before.function.jump_tables.val ++ [target] ∧
      after.height = before.height ∧
      TableTargetCode before after depth := by
  obtain ⟨target,budget,table,targetEq,tableEq,branchCall⟩ :=
    compiler_table_branch_success ops law before after index depth lookup accepted
  let staged := {before with budget,function := {before.function with jump_tables := table}}
  change runtime.compiler.control.FunctionCompiler.branch ops staged depth 1#u32 false = .ok (.Ok (),after) at branchCall
  have tables := compiler_branch_tables ops law staged after depth 1#u32 false branchCall
  have tableAfter := congrArg CompilerTables.jumpTables tables
  change after.function.jump_tables.val = table.val at tableAfter
  have height := compiler_branch_height_result ops law staged after depth 1#u32 false (.Ok ()) branchCall
  obtain ⟨frameIndex,frame,source,found,position,operands⟩ :=
    compiler_branch_arguments_success ops staged after depth 1#u32 branchCall
  refine ⟨target,targetEq,tableAfter.trans tableEq,height,?_⟩
  by_cases isLoop : frame.kind = .Loop
  · have width : source.val + frame.params.val + (1#u32).val = staged.height.val := by
      simpa only [frameBranchWidth,isLoop] using operands
    obtain ⟨code,frames⟩ := compiler_branch_loop_skip_success ops law staged frame frameIndex depth source 1#u32
      found position isLoop width after branchCall
    exact .loop frameIndex frame source found position isLoop width code frames
  · have width : source.val + frame.results.val + (1#u32).val = staged.height.val := by
      cases kind : frame.kind <;> simp_all [frameBranchWidth]
    obtain ⟨fixups,frames,_,code,site,sitePosition,appended⟩ := compiler_branch_forward_skip_success ops law staged frame frameIndex depth source 1#u32
      found position isLoop width after branchCall
    exact .forward frameIndex frame source fixups site found position isLoop width code frames appended sitePosition
end Itasca.Runtime.Compiler

end

/-! ## Branch Table Build -/

section

namespace Itasca.Runtime.Compiler
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
end Itasca.Runtime.Compiler

end
