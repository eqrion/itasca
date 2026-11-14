import Itasca.Runtime.Compiler.Local.Capacity.LiteralCapacity
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableFrames
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Control.Control.StructuredElseResolvedAppend
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableBuild
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableMetadata
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchCertificates
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableTrace

/-!
Sections, each formerly its own module: BranchTableEffects, BranchTableOperands, BranchTableSites, BranchTableSafetyEffects.
-/

/-! ## BranchTableEffects -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Uniform successful callback effects, including an unreachable source path. -/
theorem compiler_br_table_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (dominance : before.function.jump_tables.val.length≤before.function.code.val.length)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types=.ok (.Ok (),after)) :
    TableFixed before after ∧ SourceProgress before after ∧ after.next_source=state.pos ∧
    CompilerTableBoundary after ∧ after.reachable=false ∧
    after.function.code.val.length≤before.function.code.val.length+1+2*(before.table_depths.val.length+1) := by
  obtain ⟨boundary,dead⟩ := compiler_br_table_boundary ops law before after state fallback types dominance accepted
  have source := compiler_br_table_sources ops law before after state fallback types accepted
  by_cases live : before.reachable=true
  · exact ⟨compiler_br_table_fixed ops law before after state fallback types live accepted,
      source.1,source.2,boundary,dead,compiler_br_table_code_growth ops law before after state fallback types live accepted⟩
  · have deadBefore : before.reachable=false := by cases same : before.reachable <;> simp_all
    obtain ⟨fixed,code,_,_,_,_,_,_⟩ := compiler_br_table_dead_effect ops law before after state fallback types deadBefore accepted
    exact ⟨fixed,source.1,source.2,boundary,dead,by rw [code]; omega⟩
end Itasca.Runtime.Compiler

end

/-! ## BranchTableOperands -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Static source operand suffixes for every independently decoded table arm.
The selector has already been separated from `stack`. -/
def TableOperandScopes (scopes : List SourceScope) (stack : List valtype)
    (depths : List U32) : Prop :=
  ∀ depth ∈ depths, ∃ scope discarded,
    scopes.reverse[depth.val]? = some scope ∧ scope.entered = true ∧
    stack = scope.front ++ discarded ++ scope.branchTypes

private theorem paired_shapes_lookup {locals scopes frames}
    (paired : List.Forall₂ (ScopeFrameShape locals) scopes frames)
    (index : Nat) (scope : SourceScope) (frame : runtime.compiler.Frame)
    (source : scopes[index]? = some scope) (physical : frames[index]? = some frame) :
    ScopeFrameShape locals scope frame := by
  induction paired generalizing index with
  | nil => simp at source
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at source physical
      subst scope frame
      exact head
    | succ index => exact ih index source physical

 theorem table_scope_shape {locals scopes frames}
    (paired : List.Forall₂ (ScopeFrameShape locals) scopes frames)
    (index depth : Nat) (scope : SourceScope) (frame : runtime.compiler.Frame)
    (source : scopes.reverse[depth]? = some scope) (physical : frames[index]? = some frame)
    (position : index+depth+1=frames.length) : ScopeFrameShape locals scope frame := by
  have bound : depth < scopes.length := by
    have bound := (List.getElem?_eq_some_iff.mp source).1
    simpa only [List.length_reverse] using bound
  have lengths := paired.length_eq
  have coordinate : scopes.length-1-depth=index := by omega
  rw [List.getElem?_reverse bound,coordinate] at source
  exact paired_shapes_lookup paired index scope frame source physical

/-- Actual checked subtraction fixes the source slot, while the canonical
source suffix and retained frame shape fix its types and destination. -/
theorem table_operand_layout {locals stack scope label frame discarded}
    (shape : ScopeFrameShape locals scope frame) (typedLabel : ScopeLabel scope label)
    (entered : scope.entered=true)
    (input : stack=scope.front++discarded++scope.branchTypes)
    (source height : U32) (heightEq : height.val=slots locals+slots stack+1)
    (sourceEq : source.val+(frameBranchWidth frame).val+1=height.val) :
    BranchLayout locals stack label frame.height source (frameBranchWidth frame) := by
  have width : (frameBranchWidth frame).val = slots scope.branchTypes := shape.branch_width
  have destination := shape.height entered
  refine ⟨discarded,?_,?_,?_,?_⟩
  · simpa only [typedLabel.front,typedLabel.branchTypes] using input
  · simpa only [typedLabel.front] using destination
  · rw [typedLabel.front]
    rw [input,slots_append,slots_append] at heightEq
    rw [slots_append]
    omega
  · simpa only [typedLabel.branchTypes] using width
end Itasca.Runtime.Compiler

end

/-! ## BranchTableSites -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Newly appended forward holes remain valid instruction sites; unrelated
frame guards and holes remain valid under the exact appended fragment. -/
theorem TableTargetCode.frame_sites {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depth : U32}
    (effect : TableTargetCode before after depth)
    (sites : ∀ frame ∈ before.frames.val, FrameSites before.function.code.val frame) :
    ∀ frame ∈ after.frames.val, FrameSites after.function.code.val frame := by
  cases effect with
  | loop index frame source lookup position kind operands code frames =>
    intro current member
    rw [frames] at member
    simpa only [code] using (sites current member).extend (branchInstructions frame.height source frame.params frame.start_pc)
  | forward index frame source fixups site lookup position kind operands code frames appended sitePosition =>
    intro current member
    rw [frames] at member
    rcases List.mem_or_eq_of_mem_set member with previous | rfl
    · simpa only [code] using (sites current previous).extend (branchInstructions frame.height source frame.results core.num.U32.MAX)
    · have valid := sites frame (List.mem_of_getElem? lookup)
      simpa only [code] using valid.add_branch frame.height source frame.results core.num.U32.MAX site fixups appended sitePosition

theorem TableTargetsBuilt.frame_sites {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depths targets : List U32}
    (built : TableTargetsBuilt before after depths targets)
    (sites : ∀ frame ∈ before.frames.val, FrameSites before.function.code.val frame) :
    ∀ frame ∈ after.frames.val, FrameSites after.function.code.val frame := by
  induction built with
  | nil => exact sites
  | cons _ _ _ _ _ _ effect rest ih => exact ih (effect.frame_sites sites)
end Itasca.Runtime.Compiler

end

/-! ## BranchTableSafetyEffects -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

theorem TableTargetCode.fixup_budget {A} {before after : runtime.compiler.FunctionCompiler A}
    {depth : U32} (effect : TableTargetCode before after depth)
    (budget : FixupBudget before.frames.val before.function.code.val.length) :
    FixupBudget after.frames.val after.function.code.val.length := by
  obtain ⟨fragment,code,growth⟩ := effect.code_prefix
  have larger : before.function.code.val.length + 1 ≤ after.function.code.val.length := by
    simp only [code,List.length_append]; omega
  cases effect with
  | loop index frame source lookup position kind operands code frames =>
    rw [frames]
    exact budget.mono (by omega)
  | forward index frame source fixups site lookup position kind operands code frames appended sitePosition =>
    rw [frames]
    exact budget.branch index.val frame fixups lookup (by simp [appended]) larger

theorem compiler_table_branch_cursor {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32) (lookup : before.table_depths.val[index.val]? = some depth)
    (accepted : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (),after)) :
    after.next_source = before.next_source := by
  obtain ⟨target,budget,table,_,_,called⟩ :=
    compiler_table_branch_success ops law before after index depth lookup accepted
  let staged := {before with budget,function := {before.function with jump_tables := table}}
  change runtime.compiler.control.FunctionCompiler.branch ops staged depth 1#u32 false = .ok (.Ok (),after) at called
  exact compiler_branch_cursor ops law staged after depth 1#u32 false called
/-- Allocation room retained while lowering a finite list of table targets. -/
structure TableLoopSafe {A} (compiler : runtime.compiler.FunctionCompiler A)
    (index limit : Nat) : Prop where
  aligned : SourceAligned compiler
  depths : ∀ depth ∈ compiler.table_depths.val, depth.val < compiler.frames.val.length
  fixups : FixupBudget compiler.frames.val compiler.function.code.val.length
  room : compiler.function.code.val.length + 2 * (compiler.table_depths.val.length - index) ≤ limit
  tables : compiler.function.jump_tables.val.length ≤ compiler.function.code.val.length
  coordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max

theorem TableLoopSafe.advance {A} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {before after : runtime.compiler.FunctionCompiler A} {index : Usize} {limit : Nat}
    (safe : TableLoopSafe before index.val limit)
    (inside : index.val < before.table_depths.val.length)
    (accepted : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (),after)) :
    TableLoopSafe after (index.val+1) limit := by
  let depth := before.table_depths.val[index.val]
  have lookup : before.table_depths.val[index.val]? = some depth := by simp [depth,inside]
  obtain ⟨target,targetPC,appended,height,effect⟩ :=
    compiler_table_target_code ops law before after index depth lookup accepted
  have same := compiler_table_branch_depths ops before after index (.Ok ()) accepted
  have growth := effect.code_growth
  obtain ⟨fragment,code,positive⟩ := effect.code_prefix
  have grows : before.function.code.val.length + 1 ≤ after.function.code.val.length := by
    simp only [code,List.length_append]; omega
  have metadata := (compiler_table_branch_fixed ops law before after index depth lookup accepted).stable.fields
  have cursor := compiler_table_branch_cursor ops law before after index depth lookup accepted
  refine ⟨(compiler_table_branch_sources ops law before after index accepted).aligned safe.aligned,
    ?_,effect.fixup_budget safe.fixups,?_,?_,?_⟩
  · rw [same,effect.frame_length]
    exact safe.depths
  · rw [same]
    have room := safe.room
    omega
  · simp only [appended,List.length_append,List.length_singleton]
    have tables := safe.tables
    omega
  · rw [metadata.2.2.2.2.2.2.2.1,cursor]
    exact safe.coordinate
end Itasca.Runtime.Compiler

end
