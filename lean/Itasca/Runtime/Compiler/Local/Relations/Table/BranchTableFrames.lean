import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchContracts
import Itasca.Runtime.Compiler.Local.Lowering.Emission.CopyContracts
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Source.SourceTactics
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Frame
import Itasca.Runtime.Compiler.Local.Relations.Layout.ValueRegions
import Itasca.Runtime.Compiler.Local.Relations.Table.ControlTablePreservation
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableTrace
import Itasca.Runtime.Compiler.Local.Relations.Table.TableDepths
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeFrames
import Itasca.Runtime.Compiler.Local.Initializer.SegmentEmissionContracts
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CallbackRetention
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables

/-!
Proofs for Runtime / Compiler / Local / Relations / Table.

This module collects BranchTableBuild, BranchTableMetadata, BranchTableFrames.
Each section documents its contracts and consumers.
-/

/-! ## BranchTableBuild -/

section

open Itasca.Representation

/-!
Construction of br_table targets with their emitted heights and table correspondence. TableTargetsBuilt records the target-by-target invariant consumed by loop proofs.
-/

/-! ## Branch Table Height -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation
set_option maxRecDepth 4096

theorem compiler_branch_height_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status, after)) :
    after.height = before.height := by
  have frame := (runtime.compiler.control.FunctionCompiler.branch.inv ops before after depth skip conditional status accepted).frame
  rw [frame]

end Itasca.Compiler

end

/-! ## Branch Table Target -/

section

namespace Itasca.Compiler
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
end Itasca.Compiler

end

/-! ## Branch Table Build -/

section

namespace Itasca.Compiler
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
end Itasca.Compiler

end

end

/-! ## BranchTableMetadata -/

section

/-! ## BranchTableLower -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation
set_option maxRecDepth 4096

/-- Successful lowering retains the exact side-table start/count, selector
lookup, dispatch emission, and finite sequence of target branches. -/
theorem compiler_lower_table_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before = .ok (.Ok (),after)) :
    ∃ start len selector emitted,
      start.val = before.function.jump_tables.val.length ∧
      len.val = before.table_depths.val.length ∧
      runtime.compiler.FunctionCompiler.operand ops before 1#usize = .ok (.Ok selector) ∧
      Emitted before emitted (.JumpTable selector start len) ∧
      TableBranchRun ops emitted 0 after := by
  obtain ⟨start, length, selector, emitted, output, startEq, lengthEq, operand, emission, loopCall, successful, same⟩ :=
    (runtime.compiler.control.FunctionCompiler.lower_table_branches.inv ops before after (.Ok ()) accepted).success law
  have trace := (compiler_table_loop_trace ops law emitted 0#usize (.Ok ()) output loopCall successful).2
  rw [same] at trace
  exact ⟨start, length, selector, emitted, startEq, lengthEq, operand, emission.emitted, trace⟩

end Itasca.Compiler

end

/-! ## BranchTableCallback -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

/-- Label collection changes only its buffer and allocation accounting. -/
theorem compiler_table_label_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
      ops before state depth = .ok (.Ok (),after)) :
    ∃ budget depths, after = {before with budget, table_depths := depths} ∧
      depths.val = before.table_depths.val ++ [depth] := by
  have effect := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.inv ops before after state depth (.Ok ()) accepted
  exact ⟨after.budget, after.table_depths, effect.frame, effect.appended law⟩

/-- The final callback lowers all previously collected labels plus the default,
clears its private buffer, and observes the unreachable validator continuation. -/
theorem compiler_br_table_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (default : U32) (types : Itasca.signature.ResultType)
    (live : before.reachable = true)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state default types = .ok (.Ok (),after)) :
    ∃ budget depths lowered cleared,
      depths.val = before.table_depths.val ++ [default] ∧
      runtime.compiler.control.FunctionCompiler.lower_table_branches ops
        {before with budget,table_depths := depths} = .ok (.Ok (),lowered) ∧
      cleared.val = [] ∧
      runtime.compiler.FunctionCompiler.observe ops
        {lowered with reachable := false,table_depths := cleared} state = .ok (.Ok (),after) := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table.inv ops before after state default types (.Ok ()) accepted with
  | @live labeled lowered cleared _ _ labelCall reachable lowerCall clearCall observed =>
    have label := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.inv ops before labeled state default (.Ok ()) labelCall
    have empty := runtime.clear.spec lowered.table_depths
    rw [clearCall, WP.spec_ok] at empty
    refine ⟨labeled.budget, labeled.table_depths, lowered, cleared, label.appended law, ?_, empty, observed⟩
    rw [← label.frame]
    exact lowerCall
  | @dead labeled cleared _ _ labelCall dead clearCall observed =>
    have frame := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.inv ops before labeled state default (.Ok ()) labelCall).frame
    rw [frame] at dead
    simp only [live, Bool.true_eq_false] at dead

end Itasca.Compiler

end

/-! ## BranchTableMetadata -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- BR_TABLE may append dispatch targets and update frame fixups, while all
other function tables and source/local metadata remain fixed. -/
structure TableFixed {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop where
  stable : CompilerStable before after
  controls : after.function.controls=before.function.controls
  indirect : after.function.indirect.val=before.function.indirect.val
  simd : after.function.simd.val=before.function.simd.val
  constants : after.function.v128_pool.val=before.function.v128_pool.val

theorem TableFixed.refl {A : Type} (compiler : runtime.compiler.FunctionCompiler A) : TableFixed compiler compiler :=
  ⟨.refl _,rfl,rfl,rfl,rfl⟩

theorem TableFixed.trans {A : Type} {before middle after : runtime.compiler.FunctionCompiler A}
    (first : TableFixed before middle) (second : TableFixed middle after) : TableFixed before after :=
  ⟨first.stable.trans second.stable,second.controls.trans first.controls,second.indirect.trans first.indirect,
    second.simd.trans first.simd,second.constants.trans first.constants⟩

theorem compiler_table_branch_fixed {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32) (lookup : before.table_depths.val[index.val]?=some depth)
    (accepted : runtime.compiler.control.FunctionCompiler.table_branch ops before index=.ok (.Ok (),after)) :
    TableFixed before after := by
  obtain ⟨target,budget,table,_,_,called⟩ := compiler_table_branch_success ops law before after index depth lookup accepted
  let staged := {before with budget,function := {before.function with jump_tables := table}}
  change runtime.compiler.control.FunctionCompiler.branch ops staged depth 1#u32 false=.ok (.Ok (),after) at called
  have stable := compiler_branch_stable_result ops law staged after depth 1#u32 false (.Ok ()) called
  have controls := compiler_branch_controls_result ops law staged after depth 1#u32 false (.Ok ()) called
  have tables := compiler_branch_tables ops law staged after depth 1#u32 false called
  exact ⟨⟨stable.metadata,stable.capacity⟩,controls,congrArg CompilerTables.indirect tables,
    congrArg CompilerTables.simd tables,congrArg CompilerTables.constants tables⟩

theorem TableBranchRun.fixed {A : Type} {ops : runtime.platform.Alloc A}
    (law : Platform.AllocCorrect ops) {before after : runtime.compiler.FunctionCompiler A}
    {index : Nat} (run : TableBranchRun ops before index after) : TableFixed before after := by
  induction run with
  | done => exact .refl _
  | @cons before middle after index inside called rest ih =>
    exact (compiler_table_branch_fixed ops law before middle index before.table_depths.val[index.val]
      (List.getElem?_eq_getElem inside) called).trans ih

theorem compiler_lower_table_fixed {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before=.ok (.Ok (),after)) :
    TableFixed before after := by
  obtain ⟨start,len,selector,emitted,_,_,_,emission,run⟩ := compiler_lower_table_success ops law before after accepted
  have stable := emission.stable
  obtain ⟨budget,code,sources,rfl,_,_⟩ := emission
  exact (show TableFixed before _ from ⟨stable,rfl,rfl,rfl,rfl⟩).trans (run.fixed law)

theorem compiler_br_table_fixed {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (live : before.reachable=true)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types=.ok (.Ok (),after)) : TableFixed before after := by
  obtain ⟨budget,depths,lowered,cleared,_,loweredCall,_,observed⟩ :=
    compiler_br_table_success ops law before after state fallback types live accepted
  have loweredFixed := compiler_lower_table_fixed ops law {before with budget,table_depths := depths} lowered loweredCall
  have observation := compiler_observe_frame ops law {lowered with reachable := false,table_depths := cleared} state
  rw [observed,WP.spec_ok] at observation
  have observedStable := compiler_observe_stable ops law {lowered with reachable := false,table_depths := cleared} after state observed
  have finalStable : CompilerStable lowered after := ⟨observedStable.metadata,observedStable.capacity⟩
  have finalFixed : TableFixed lowered after := by
    refine ⟨finalStable,?_,?_,?_,?_⟩ <;> rw [show after = _ from observation]
  exact (show TableFixed before lowered from ⟨⟨loweredFixed.stable.metadata,loweredFixed.stable.capacity⟩,
    loweredFixed.controls,loweredFixed.indirect,loweredFixed.simd,loweredFixed.constants⟩).trans finalFixed
end Itasca.Compiler

end

end

/-! ## BranchTableFrames -/

section

/-! ## BranchTableProduction -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- An accepted dispatch emits one header followed by the exact ordered target
fragments, with the side-table entries and default count tied to actual buffers. -/
theorem compiler_lower_table_production {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before = .ok (.Ok (),after)) :
    ∃ start len selector emitted targets,
      start.val = before.function.jump_tables.val.length ∧
      len.val = before.table_depths.val.length ∧
      runtime.compiler.FunctionCompiler.operand ops before 1#usize = .ok (.Ok selector) ∧
      Emitted before emitted (.JumpTable selector start len) ∧
      TableTargetsBuilt emitted after before.table_depths.val targets ∧
      after.function.jump_tables.val = before.function.jump_tables.val ++ targets ∧
      targets.length = len.val ∧ after.height = before.height ∧
      before.function.code.val.length + 1 ≤ after.function.code.val.length := by
  obtain ⟨start,len,selector,emitted,startEq,lenEq,operand,emission,run⟩ :=
    compiler_lower_table_success ops law before after accepted
  obtain ⟨targets,built⟩ := run.built law
  simp only [List.drop_zero] at built
  obtain ⟨budget,code,sources,emittedEq,codeEq,sourcesEq⟩ := emission
  subst emitted
  obtain ⟨fragment,codeAfter,lengthAfter⟩ := built.code_prefix
  have headerBound : before.function.code.val.length + 1 ≤ after.function.code.val.length := by
    rw [codeAfter]
    simp only [List.length_append]
    rw [codeEq]
    simp
  exact ⟨start,len,selector,_,targets,startEq,lenEq,operand,
    ⟨budget,code,sources,rfl,codeEq,sourcesEq⟩,built,built.tables,
    built.length.trans lenEq.symm,built.height,headerBound⟩
end Itasca.Compiler

end

/-! ## BranchTableCallbackProduction -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- The accepted terminal callback produces the header and every ordered target
fragment, then retains their exact code/side table through final observation. -/
theorem compiler_br_table_production {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (default : U32) (types : Itasca.signature.ResultType)
    (live : before.reachable = true)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state default types = .ok (.Ok (),after)) :
    ∃ (budget : runtime.compiler.Budget A) (depths : alloc.vec.Vec U32)
      (start len selector : U32) (emitted lowered : runtime.compiler.FunctionCompiler A) (targets : List U32),
      depths.val = before.table_depths.val ++ [default] ∧
      start.val = before.function.jump_tables.val.length ∧
      len.val = before.table_depths.val.length + 1 ∧
      Emitted {before with budget,table_depths := depths} emitted (.JumpTable selector start len) ∧
      TableTargetsBuilt emitted lowered (before.table_depths.val ++ [default]) targets ∧
      after.function.code = lowered.function.code ∧
      after.frames = lowered.frames ∧
      after.function.jump_tables.val = before.function.jump_tables.val ++ targets ∧
      targets.length = len.val ∧
      after.table_depths.val = [] ∧ after.reachable = false ∧
      before.function.code.val.length + 1 ≤ after.function.code.val.length := by
  obtain ⟨budget,depths,lowered,cleared,depthsEq,loweredCall,clearedEq,observeCall⟩ :=
    compiler_br_table_success ops law before after state default types live accepted
  obtain ⟨start,len,selector,emitted,targets,startEq,lenEq,operand,emission,built,tables,count,height,header⟩ :=
    compiler_lower_table_production ops law {before with budget,table_depths := depths} lowered loweredCall
  have observation := compiler_observe_frame ops law {lowered with reachable := false,table_depths := cleared} state
  rw [observeCall,WP.spec_ok] at observation
  dsimp only [ObserveFrame] at observation
  rw [observation]
  refine ⟨budget,depths,start,len,selector,emitted,lowered,targets,depthsEq,startEq,?_,
    emission,?_,rfl,rfl,tables,count,clearedEq,rfl,header⟩
  · simpa only [depthsEq,List.length_append,List.length_singleton] using lenEq
  · simpa only [depthsEq] using built
end Itasca.Compiler

end

/-! ## BranchTableDead -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation
set_option maxRecDepth 4096

/-- Unreachable table instructions still consume and clear their label buffer,
while leaving the entire code, relocation table and frame stack unchanged. -/
theorem compiler_br_table_dead_effect {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (dead : before.reachable=false)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types=.ok (.Ok (),after)) :
    TableFixed before after ∧ after.function.code=before.function.code ∧
    after.function.jump_tables=before.function.jump_tables ∧ after.frames=before.frames ∧
    after.table_depths.val=[] ∧ after.reachable=false ∧
    SourceProgress before after ∧ after.next_source=state.pos := by
  have sources := compiler_br_table_sources ops law before after state fallback types accepted
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table.inv ops before after state fallback types (.Ok ()) accepted with
  | @live labeled lowered cleared _ _ labelCall live lowerCall clearCall observed =>
    have frame := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.inv ops before labeled state fallback (.Ok ()) labelCall).frame
    rw [frame] at live
    simp only [dead, Bool.false_eq_true] at live
  | @dead labeled cleared _ _ labelCall dormant clearCall observed =>
    have frame := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.inv ops before labeled state fallback (.Ok ()) labelCall).frame
    have empty := runtime.clear.spec labeled.table_depths
    rw [clearCall, WP.spec_ok] at empty
    have kept := compiler_observe_frame_raw ops {labeled with table_depths := cleared} state (.Ok ()) after observed
    have stable := compiler_observe_stable ops law {labeled with table_depths := cleared} after state observed
    rw [frame] at kept stable
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, sources⟩
    · refine ⟨⟨stable.metadata, stable.capacity⟩, ?_, ?_, ?_, ?_⟩ <;> rw [kept]
    · rw [kept]
    · rw [kept]
    · rw [kept]
    · rw [kept]
      exact empty
    · rw [kept]
      exact dead

end Itasca.Compiler

end

/-! ## BranchTableFrames -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

private theorem paired_set_right {α β : Type} {R : α → β → Prop} {left right}
    (paired : List.Forall₂ R left right) (index : Nat) (before after : β)
    (found : right[index]? = some before) (change : ∀ a, R a before → R a after) :
    List.Forall₂ R left (right.set index after) := by
  induction paired generalizing index with
  | nil => simp at found
  | @cons a b left right related rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at found
      subst b
      exact .cons (change a related) rest
    | succ index => exact .cons related (ih index found)

/-- Every arm preserves the original source-scope geometry. Forward arms only
add a relocation and record exit liveness; loop frames remain untouched. -/
theorem TableTargetCode.scope_shapes {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depth : U32}
    (effect : TableTargetCode before after depth) (locals : List valtype) (scopes : List SourceScope)
    (paired : List.Forall₂ (ScopeFrameShape locals) scopes before.frames.val) :
    List.Forall₂ (ScopeFrameShape locals) scopes after.frames.val := by
  cases effect with
  | loop index frame source lookup position kind operands code frames => simpa only [frames] using paired
  | forward index frame source fixups site lookup position kind operands code frames appended sitePosition =>
    rw [frames]
    exact paired_set_right paired index.val frame _ lookup (fun _ shape => shape.record_branch fixups kind)

theorem TableTargetsBuilt.scope_shapes {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depths targets : List U32}
    (built : TableTargetsBuilt before after depths targets) (locals : List valtype) (scopes : List SourceScope)
    (paired : List.Forall₂ (ScopeFrameShape locals) scopes before.frames.val) :
    List.Forall₂ (ScopeFrameShape locals) scopes after.frames.val := by
  induction built with
  | nil => exact paired
  | cons _ _ _ _ _ _ effect rest ih => exact ih (effect.scope_shapes locals scopes paired)

/-- All emitted arms keep the physical control-stack length fixed. -/
theorem TableTargetCode.frame_length {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depth : U32}
    (effect : TableTargetCode before after depth) : after.frames.val.length = before.frames.val.length := by
  cases effect with
  | loop index frame source lookup position kind operands code frames => rw [frames]
  | forward index frame source fixups site lookup position kind operands code frames appended sitePosition =>
    simp only [frames,List.length_set]

theorem TableTargetsBuilt.frame_length {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depths targets : List U32}
    (built : TableTargetsBuilt before after depths targets) : after.frames.val.length = before.frames.val.length := by
  induction built with
  | nil => rfl
  | cons _ _ _ _ _ _ effect rest ih => exact ih.trans effect.frame_length
end Itasca.Compiler

end

end
