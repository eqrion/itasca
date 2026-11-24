import Itasca.Runtime.Compiler.Local.Capacity.ControlAvailability
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableFrames
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CallbackRetention
import Itasca.Runtime.Compiler.Local.Control.StructuredElseResolvedAppend
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlCoordinates
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableTrace
import Itasca.Runtime.Compiler.Local.Relations.Table.TableDepths
import Itasca.Runtime.Compiler.Local.Lowering.LoweringLocal
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ConsumedPrefix
import Itasca.Runtime.Compiler.Local.Control.CodeSegmentsAndPositions
import Itasca.Runtime.SourceMachine.EntryAndBranchTables
import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeFrames
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchSkipSafety
import Itasca.Runtime.Compiler.Local.Lowering.Integer.Safety

/-!
Proofs for Runtime / Compiler / Local / Relations / Table.

This module collects BranchTableSafetyEffects, BranchTable, BranchTableCallbackSafety.
Each section documents its contracts and consumers.
-/

/-! ## BranchTableSafetyEffects -/

section

open Itasca.Representation

/-! ## BranchTableEffects -/

section

namespace Itasca.Compiler
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
end Itasca.Compiler

end

/-! ## BranchTableOperands -/

section

namespace Itasca.Compiler
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
end Itasca.Compiler

end

/-! ## BranchTableSites -/

section

namespace Itasca.Compiler
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
end Itasca.Compiler

end

/-! ## BranchTableSafetyEffects -/

section

namespace Itasca.Compiler
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
end Itasca.Compiler

end

end

/-! ## BranchTable -/

section

open Itasca.Representation

/-! ## BranchTableCallbackLayout -/

section

/-!
Resolved br_table target layouts and their callback certificate. Per-target resolution composes into the built table and final source prefix.
-/

/-! ## Branch Table Resolution -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Resolve one physical table arm under any admissible completion plan. The
plan is rewound without adding a synthetic source BR instruction. -/
theorem TableTargetCode.resolve {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depth : U32}
    (effect : TableTargetCode before after depth) (locals : List valtype)
    (labels : List LabelTarget) (groups : List FixupTarget)
    (sites : ∀ frame ∈ before.frames.val, FrameSites before.function.code.val frame)
    (plans : FramePlans after.function.code.val.length locals after.frames.val labels groups) :
    ∃ previous label guard frame source index,
      FramePlans before.function.code.val.length locals before.frames.val labels previous ∧
      labels[depth.val]? = some label ∧ label.branchLive = true ∧
      before.frames.val[index]? = some frame ∧ index + depth.val + 1 = before.frames.val.length ∧
      FrameFuture before.function.code.val.length locals frame label guard ∧
      source.val + (frameBranchWidth frame).val + 1 = before.height.val ∧
      resolvedCode after.function.code.val groups = resolvedCode before.function.code.val previous ++
        branchInstructions frame.height source (frameBranchWidth frame) label.target := by
  obtain ⟨fragment,codeSuffix,_⟩ := effect.code_prefix
  have order : before.function.code.val.length ≤ after.function.code.val.length := by
    simp only [codeSuffix,List.length_append]
    omega
  cases effect with
  | loop index frame source lookup position kind operands code frames =>
    have prior : FramePlans before.function.code.val.length locals before.frames.val labels groups := by
      rw [← frames]
      exact plans.before order
    obtain ⟨label,guard,labelAt,future⟩ := prior.lookup lookup position
    refine ⟨groups,label,guard,frame,source,index.val,prior,labelAt,future.loopLive kind,
      lookup,position,future,?_,?_⟩
    · simpa only [frameBranchWidth,kind] using operands
    · rw [code,resolved_code_append_code _ _ _ (prior.inside sites),future.loopTarget kind]
      simp only [frameBranchWidth,kind]
  | forward index frame source fixups site lookup position kind operands code frames appended sitePosition =>
    obtain ⟨label,earlier,later,labelAt,live,previous,grouped⟩ := plans.before_mark fixups frames lookup position
    have prior := previous.before order
    obtain ⟨sameLabel,guard,sameAt,future⟩ := prior.lookup lookup position
    have labelEq : sameLabel = label := Option.some.inj (sameAt.symm.trans labelAt)
    subst sameLabel
    have width : frameBranchWidth frame = frame.results := by
      cases equation : frame.kind <;> simp_all [frameBranchWidth]
    refine ⟨_,label,guard,frame,source,index.val,prior,labelAt,live,lookup,position,future,?_,?_⟩
    · simpa only [width] using operands
    · rw [code,grouped,appended,width]
      exact resolved_code_new_br before.function.code.val earlier later ⟨frame.fixups.val,label.target⟩
        frame.height source frame.results core.num.U32.MAX site sitePosition (prior.inside sites)
end Itasca.Compiler

end

/-! ## Branch Table Resolved -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- All ordered arms resolve under one final completion plan. Each target is a
real side-table PC with the canonical branch layout and a contained code fragment;
no fictitious source branch sequence is introduced while rewinding fixups. -/
theorem TableTargetsBuilt.resolved {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depths targets : List U32}
    (built : TableTargetsBuilt before after depths targets)
    (locals stack : List valtype) (scopes : List SourceScope) (labels : List LabelTarget)
    (groups : List FixupTarget)
    (paired : List.Forall₂ (ScopeFrameShape locals) scopes before.frames.val)
    (labelShapes : List.Forall₂ ScopeLabel scopes.reverse labels)
    (inputs : TableOperandScopes scopes stack depths)
    (height : before.height.val = slots locals+slots stack+1)
    (sites : ∀ frame ∈ before.frames.val, FrameSites before.function.code.val frame)
    (plans : FramePlans after.function.code.val.length locals after.frames.val labels groups) :
    ∃ previous extra,
      FramePlans before.function.code.val.length locals before.frames.val labels previous ∧
      resolvedCode after.function.code.val groups = resolvedCode before.function.code.val previous ++ extra ∧
      ∀ (index : Nat) (depth : U32), depths[index]? = some depth →
        ∃ entry, targets[index]? = some entry ∧
          BranchTableEntry locals labels stack (resolvedCode after.function.code.val groups)
            (.mk_uN depth.val) entry after.function.code.val.length := by
  induction built generalizing groups with
  | nil =>
    exact ⟨groups,[],plans,by simp,by intro index depth lookup; simp at lookup⟩
  | @cons before middle after depths targets head target targetPC appended sameHeight sameDepths effect rest ih =>
    have remainingInputs : TableOperandScopes scopes stack depths := fun depth member =>
      inputs depth (List.mem_cons_of_mem _ member)
    obtain ⟨middleGroups,tailCode,middlePlans,tailResolved,tailEntries⟩ :=
      ih groups (effect.scope_shapes locals scopes paired) remainingInputs
        (by simpa only [sameHeight] using height) (effect.frame_sites sites) plans
    obtain ⟨previous,label,guard,frame,source,index,priorPlans,labelAt,live,
      frameAt,position,future,sourceEq,armResolved⟩ := effect.resolve locals labels middleGroups sites middlePlans
    obtain ⟨scope,discarded,scopeAt,entered,input⟩ := inputs head (by simp)
    have shape := table_scope_shape paired index head.val scope frame scopeAt frameAt position
    have labelShape := scope_labels_lookup labelShapes scopeAt labelAt
    have layout := table_operand_layout shape labelShape entered input source before.height height sourceEq
    let fragment := branchInstructions frame.height source (frameBranchWidth frame) label.target
    have resolved : resolvedCode after.function.code.val groups =
        resolvedCode before.function.code.val previous ++ (fragment++tailCode) := by
      rw [tailResolved,armResolved,List.append_assoc]
    have lengthArm : middle.function.code.val.length =
        before.function.code.val.length+fragment.length := by
      have equation := congrArg List.length armResolved
      simpa only [resolved_code_length,List.length_append] using equation
    have middleBound : middle.function.code.val.length ≤ after.function.code.val.length := by
      obtain ⟨suffix,code,_⟩ := rest.code_prefix
      simp only [code,List.length_append]
      omega
    have firstEntry : BranchTableEntry locals labels stack (resolvedCode after.function.code.val groups)
        (.mk_uN head.val) target after.function.code.val.length := by
      refine ⟨label,frame.height,source,frameBranchWidth frame,middle.function.code.val.length,
        labelAt,live,layout,?_,middleBound,?_⟩
      · refine ⟨resolvedCode before.function.code.val previous,tailCode,?_,?_,?_⟩
        · simpa only [List.append_assoc,fragment] using resolved
        · simpa only [resolved_code_length] using targetPC.symm
        · simpa only [targetPC,fragment] using lengthArm
      · simp only [resolved_code_length]
        exact le_rfl
    refine ⟨previous,fragment++tailCode,priorPlans,resolved,?_⟩
    intro selected depth lookup
    cases selected with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at lookup
      subst depth
      exact ⟨target,rfl,firstEntry⟩
    | succ selected =>
      simp only [List.getElem?_cons_succ] at lookup ⊢
      exact tailEntries selected depth lookup
end Itasca.Compiler

end

/-! ## Branch Table Layout Production -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Successful actual lowering supplies the complete retained-table certificate
under source stack/scope typing and any admissible later fixup completion. -/
theorem compiler_lower_table_layout_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (locals stack : List valtype) (scopes : List SourceScope) (labels : List LabelTarget)
    (depths : List U32) (fallback : U32) (groups : List FixupTarget)
    (buffer : before.table_depths.val = depths++[fallback])
    (layout : CompilerLayout before (stack++[.I32])) (localTypes : compilerLocals before=locals)
    (paired : List.Forall₂ (ScopeFrameShape locals) scopes before.frames.val)
    (labelShapes : List.Forall₂ ScopeLabel scopes.reverse labels)
    (inputs : TableOperandScopes scopes stack (depths++[fallback]))
    (dominance : before.function.jump_tables.val.length ≤ before.function.code.val.length)
    (sites : ∀ frame ∈ before.frames.val, FrameSites before.function.code.val frame)
    (plans : FramePlans after.function.code.val.length locals after.frames.val labels groups)
    (accepted : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before=.ok (.Ok (),after)) :
    ∃ previous start len selector,
      FramePlans before.function.code.val.length locals before.frames.val labels previous ∧
      BranchTableLayout after.function.jump_tables.val locals labels stack
        (resolvedCode after.function.code.val groups) (depths.map (fun d => .mk_uN d.val)) (.mk_uN fallback.val)
        before.function.code.val.length after.function.code.val.length selector start len ∧
      before.function.code.val.length+1≤after.function.code.val.length ∧
      after.function.jump_tables.val.length≤after.function.code.val.length ∧
      ∃ extra, resolvedCode after.function.code.val groups =
        resolvedCode before.function.code.val previous ++ (.JumpTable selector start len :: extra) := by
  obtain ⟨start,len,selector,emitted,targets,startEq,lenEq,operandCall,emission,built,tables,count,sameHeight,header⟩ :=
    compiler_lower_table_production ops law before after accepted
  obtain ⟨selected,selectedCall,selectorEq⟩ := last_operand ops before stack .I32 layout
  have selectorSame : selector=selected := by
    rw [selectedCall] at operandCall
    exact (core.result.Result.Ok.inj (Result.ok_injective operandCall)).symm
  subst selected
  rw [localTypes] at selectorEq
  rw [buffer] at built
  obtain ⟨budget,code,sources,emittedEq,codeEq,sourcesEq⟩ := emission
  subst emitted
  have height : before.height.val=slots locals+slots stack+1 := by
    have h := layout.height
    simp only [localTypes,slots_append,slots,width,List.foldl_cons,List.foldl_nil] at h
    omega
  have emittedSites : ∀ frame ∈ before.frames.val, FrameSites code.val frame := by
    intro frame member
    simpa only [codeEq] using (sites frame member).extend [.JumpTable selector start len]
  have emittedDominance : before.function.jump_tables.val.length≤code.val.length := by
    rw [codeEq]
    simp only [List.length_append,List.length_singleton]
    omega
  obtain ⟨previous,extra,emittedPlans,resolved,entries⟩ :=
    built.resolved locals stack scopes labels groups paired labelShapes inputs height emittedSites plans
  have order : before.function.code.val.length≤code.val.length := by simp [codeEq]
  have priorPlans : FramePlans before.function.code.val.length locals before.frames.val labels previous := emittedPlans.before order
  have headerResolved : resolvedCode code.val previous = resolvedCode before.function.code.val previous ++ [.JumpTable selector start len] := by
    rw [codeEq,resolved_code_append_code _ _ _ (priorPlans.inside sites)]
  have dispatch : (resolvedCode after.function.code.val groups)[before.function.code.val.length]? =
      some (.JumpTable selector start len) := by
    rw [resolved,headerResolved,List.append_assoc]
    simp [List.getElem?_append,resolved_code_length]
  have arithmetic := built.dispatch_arithmetic emittedDominance
  refine ⟨previous,start,len,selector,priorPlans,?_,header,built.table_dominance emittedDominance,extra,?_⟩
  swap
  · rw [resolved,headerResolved,List.append_assoc]
    rfl
  refine ⟨selectorEq,?_,dispatch,?_,?_⟩
  · simpa only [buffer,List.length_append,List.length_singleton,List.length_map] using lenEq
  · simpa only [startEq,List.length_map] using arithmetic
  · intro index depth atDepth
    have mapped : ((depths++[fallback]).map (fun d : U32 => uN.mk_uN d.val))[index]? = some depth := by
      simpa only [List.map_append,List.map_cons,List.map_nil] using atDepth
    rw [List.getElem?_map] at mapped
    cases raw : (depths++[fallback])[index]? with
    | none => simp [raw] at mapped
    | some rawDepth =>
      simp only [raw,Option.map_some,Option.some.injEq] at mapped
      subst depth
      obtain ⟨entry,entryAt,entryLayout⟩ := entries index rawDepth raw
      refine ⟨entry,?_,entryLayout⟩
      rw [tables,startEq]
      rw [List.getElem?_append_right (by omega)]
      simpa only [Nat.add_sub_cancel_left] using entryAt
end Itasca.Compiler

end

/-! ## Branch Table Callback Layout -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- The actual terminal callback retains every resolved branch-table arm and
restores the scratch-buffer/dominance boundary for the following instruction. -/
theorem compiler_br_table_layout_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (locals stack : List valtype) (scopes : List SourceScope) (labels : List LabelTarget)
    (depths : List U32) (groups : List FixupTarget)
    (buffer : before.table_depths.val = depths)
    (layout : CompilerLayout before (stack++[.I32])) (localTypes : compilerLocals before=locals)
    (paired : List.Forall₂ (ScopeFrameShape locals) scopes before.frames.val)
    (labelShapes : List.Forall₂ ScopeLabel scopes.reverse labels)
    (inputs : TableOperandScopes scopes stack (depths++[fallback]))
    (dominance : before.function.jump_tables.val.length ≤ before.function.code.val.length)
    (sites : ∀ frame ∈ before.frames.val, FrameSites before.function.code.val frame)
    (plans : FramePlans after.function.code.val.length locals after.frames.val labels groups)
    (live : before.reachable=true)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types=.ok (.Ok (),after)) :
    ∃ previous start len selector,
      FramePlans before.function.code.val.length locals before.frames.val labels previous ∧
      BranchTableLayout after.function.jump_tables.val locals labels stack
        (resolvedCode after.function.code.val groups) (depths.map (fun d => .mk_uN d.val)) (.mk_uN fallback.val)
        before.function.code.val.length after.function.code.val.length selector start len ∧
      before.function.code.val.length+1≤after.function.code.val.length ∧
      CompilerTableBoundary after ∧ after.reachable=false ∧
      ∃ extra, resolvedCode after.function.code.val groups =
        resolvedCode before.function.code.val previous ++ (.JumpTable selector start len :: extra) := by
  obtain ⟨budget,collected,lowered,cleared,collectedEq,loweredCall,clearedEq,observeCall⟩ :=
    compiler_br_table_success ops law before after state fallback types live accepted
  have observation := compiler_observe_frame ops law {lowered with reachable := false,table_depths := cleared} state
  rw [observeCall,WP.spec_ok] at observation
  dsimp only [ObserveFrame] at observation
  have codeEq : after.function.code = lowered.function.code := by rw [observation]
  have framesEq : after.frames = lowered.frames := by rw [observation]
  have tablesEq : after.function.jump_tables = lowered.function.jump_tables := by rw [observation]
  have depthsEq : after.table_depths = cleared := by rw [observation]
  have dead : after.reachable=false := by rw [observation]
  have plansLowered : FramePlans lowered.function.code.val.length locals lowered.frames.val labels groups := by
    simpa only [codeEq,framesEq] using plans
  have collectedLayout : CompilerLayout {before with budget,table_depths := collected} (stack++[.I32]) :=
    ⟨layout.localSlots,layout.localOffsets,layout.operandOffsets,layout.height,layout.capacity⟩
  obtain ⟨previous,start,len,selector,previousPlans,certificate,header,targets,extra,resolved⟩ :=
    compiler_lower_table_layout_prefix ops law {before with budget,table_depths := collected} lowered
      locals stack scopes labels depths fallback groups (by simpa only [buffer] using collectedEq)
      collectedLayout localTypes paired labelShapes inputs dominance sites plansLowered loweredCall
  refine ⟨previous,start,len,selector,previousPlans,?_,?_,?_,dead,extra,?_⟩
  · simpa only [codeEq,tablesEq] using certificate
  · simpa only [codeEq] using header
  · constructor
    · simpa only [depthsEq] using clearedEq
    · simpa only [codeEq,tablesEq] using targets
  · simpa only [codeEq] using resolved
end Itasca.Compiler

end

end

/-! ## BranchTableScopeFrames -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

private theorem frame_maps_set (frames : List runtime.compiler.Frame) (index : Nat)
    (frame : runtime.compiler.Frame) (fixups : alloc.vec.Vec Usize)
    (lookup : frames[index]? = some frame) :
    (frames.set index {frame with end_reachable := true, fixups}).map (fun f => f.map) =
      frames.map (fun f => f.map) := by
  induction frames generalizing index with
  | nil => simp at lookup
  | cons head tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
              subst frame
              rfl
    | succ index => simpa using ih index lookup

theorem TableTargetCode.frame_maps {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depth : U32}
    (effect : TableTargetCode before after depth) :
    after.frames.val.map (fun f => f.map) = before.frames.val.map (fun f => f.map) := by
  cases effect with
  | loop index frame source lookup position kind operands code frames => rw [frames]
  | forward index frame source fixups site lookup position kind operands code frames appended sitePosition =>
    rw [frames]
    exact frame_maps_set _ _ frame fixups lookup

theorem TableTargetsBuilt.frame_maps {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depths targets : List U32}
    (built : TableTargetsBuilt before after depths targets) :
    after.frames.val.map (fun f => f.map) = before.frames.val.map (fun f => f.map) := by
  induction built with
  | nil => rfl
  | cons _ _ _ _ _ _ effect rest ih => exact ih.trans effect.frame_maps

private theorem frame_scopes_of_shapes {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {locals scopes oldFrames newFrames}
    (old : List.Forall₂ (FrameScope locals before) scopes oldFrames)
    (shapes : List.Forall₂ (ScopeFrameShape locals) scopes newFrames)
    (maps : newFrames.map (fun f => f.map) = oldFrames.map (fun f => f.map))
    (suffix : List Bytecode) (code : after.function.code.val = before.function.code.val ++ suffix)
    (controls : before.function.controls.val.length ≤ after.function.controls.val.length) :
    List.Forall₂ (FrameScope locals after) scopes newFrames := by
  induction old generalizing newFrames with
  | nil => cases shapes; exact .nil
  | @cons scope frame scopes frames prior rest ih =>
    cases shapes with
    | @cons _ next _ nextFrames shape shapes =>
      simp only [List.map_cons, List.cons.injEq] at maps
      have extended := prior.extend suffix code controls
      refine .cons ⟨shape, ?_, extended.entryBound, extended.bodyBound, extended.entryCode⟩ (ih shapes maps.2)
      simpa only [maps.1] using extended.mapBound

/-- The complete live callback preserves all physical/source scope geometry,
entry code and clean dormant frames before the source zipper advances once. -/
theorem compiler_br_table_scope_frames {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    {locals parents current} (prior : ScopeFrameStack locals before parents current)
    (chain : SourceEntryChain parents current) (entered : current.entered = true)
    (sites : ∀ frame ∈ before.frames.val, FrameSites before.function.code.val frame)
    (controls : before.function.controls.val.length ≤ after.function.controls.val.length)
    (live : before.reachable = true)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types = .ok (.Ok (),after)) :
    ScopeFrameStack locals after parents current ∧ DormantFrames after.frames.val ∧
      (∀ frame ∈ after.frames.val, FrameSites after.function.code.val frame) := by
  obtain ⟨budget, depths, start, len, selector, emitted, lowered, targets,
    depthsEq, startEq, lenEq, emission, built, codeEq, framesEq, tables, count, cleared, dead, header⟩ :=
    compiler_br_table_production ops law before after state fallback types live accepted
  obtain ⟨emitBudget, code, sources, emittedEq, emittedCode, emittedSources⟩ := emission
  have emittedFrames : emitted.frames = before.frames := by rw [emittedEq]
  have emittedCodeEq : emitted.function.code.val = before.function.code.val ++ [.JumpTable selector start len] := by
    rw [emittedEq]; exact emittedCode
  obtain ⟨suffix, loweredCode, _⟩ := built.code_prefix
  have wholeCode : after.function.code.val = before.function.code.val ++ (.JumpTable selector start len :: suffix) := by
    rw [codeEq, loweredCode, emittedCodeEq]
    simp only [List.append_assoc, List.singleton_append]
  have shapes : List.Forall₂ (ScopeFrameShape locals) (parents ++ [current]) after.frames.val := by
    rw [framesEq]
    apply built.scope_shapes locals _
    simpa only [emittedFrames] using prior.frames.imp (fun _ _ p => p.toScopeFrameShape)
  have maps : after.frames.val.map (fun f => f.map) = before.frames.val.map (fun f => f.map) := by
    rw [framesEq, built.frame_maps, emittedFrames]
  have frames : ScopeFrameStack locals after parents current :=
    ⟨prior.nested, frame_scopes_of_shapes prior.frames shapes maps _ wholeCode controls⟩
  refine ⟨frames, ?_, ?_⟩
  · intro frame member
    exact DormantFrame.entered (frames.frame_entered chain entered frame member)
  · have emittedSites : ∀ frame ∈ emitted.frames.val, FrameSites emitted.function.code.val frame := by
      intro frame member
      rw [emittedFrames] at member
      simpa only [emittedCodeEq] using (sites frame member).extend [.JumpTable selector start len]
    simpa only [codeEq, framesEq] using built.frame_sites emittedSites
end Itasca.Compiler

end

/-! ## BranchTable -/

section

namespace Itasca.Compiler
open Aeneas.Std

/-- Compatibility view of the indexed branch-table layout. -/
abbrev BranchTableCode (tables : CompilerTables) := BranchTableLayout tables.jumpTables

theorem BranchTableCode.selected {tables locals labels stack code depths fallback pc next selector start len}
    (table : BranchTableCode tables locals labels stack code depths fallback pc next selector start len)
    (value : Nat) :
    ∃ entry, tables.jumpTables[start.val + Nat.min value (len.val-1)]? = some entry ∧
      BranchTableEntry locals labels stack code (SourceMachine.BrTable.select depths fallback value) entry next := by
  obtain ⟨entry,lookup,fragment⟩ := table.entries (Nat.min value depths.length)
    (SourceMachine.BrTable.select depths fallback value) (SourceMachine.BrTable.select_table depths fallback value)
  exact ⟨entry,by simpa only [table.length,Nat.add_sub_cancel] using lookup,fragment⟩

end Itasca.Compiler

end

end

/-! ## BranchTableCallbackSafety -/

section

/-!
Normal return of br_table compilation, from one target through the target loop and lowering to the compiler callback.
-/

/-! ## Branch Table Safety -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

@[step] theorem compiler_table_branch_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (index frameIndex : Usize) (depth : U32) (frame : runtime.compiler.Frame)
    (depthAt : compiler.table_depths.val[index.val]? = some depth)
    (frameAt : compiler.frames.val[frameIndex.val]? = some frame)
    (position : frameIndex.val + depth.val + 1 = compiler.frames.val.length)
    (tableFits : compiler.function.jump_tables.val.length < Usize.max)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length + 2 ≤ Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length + 2 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.table_branch ops compiler index ⦃ _ => True ⦄ := by
  apply runtime.compiler.control.FunctionCompiler.table_branch.total ops law compiler index depth depthAt tableFits
  intro budget table
  exact compiler_branch_skip_total ops law
    {compiler with budget, function := {compiler.function with jump_tables := table}}
    frame frameIndex depth 1#u32 frameAt position fixupsFit codeFits sourceFits coordinateFits

@[step] theorem compiler_table_label_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32)
    (fits : compiler.table_depths.val.length < Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
      ops compiler state depth ⦃ _ => True ⦄ := by
  exact runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.total ops law compiler state depth fits

end Itasca.Compiler

end

/-! ## Branch Table Loop Safety -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

@[step] theorem compiler_table_loop_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (limit : Nat) (limitFits : limit ≤ Usize.max)
    (held : status = .Ok () → TableLoopSafe compiler index.val limit) :
    runtime.compiler.control.FunctionCompiler.lower_table_branches_loop ops compiler index status ⦃ _ => True ⦄ := by
  apply runtime.compiler.control.FunctionCompiler.lower_table_branches_loop.spec ops
    (fun current index status => status = .Ok () → TableLoopSafe current index limit) (fun _ => True)
    ?_ ?_ compiler index status held
  · intro current i safe inside
    have held := safe rfl
    let depth := current.table_depths.val[i.val]
    have depthAt : current.table_depths.val[i.val]? = some depth := List.getElem?_eq_getElem inside
    have depthBound := held.depths depth (List.mem_of_getElem? depthAt)
    let frameIndex := Usize.ofNatCore (current.frames.val.length - depth.val - 1)
      (by have h := (alloc.vec.Vec.len current.frames).hBounds; change current.frames.val.length < 2^UScalarTy.Usize.numBits at h; omega)
    have frameBound : frameIndex.val < current.frames.val.length := by
      change current.frames.val.length - depth.val - 1 < current.frames.val.length
      omega
    let frame := current.frames.val[frameIndex.val]
    have frameAt : current.frames.val[frameIndex.val]? = some frame := List.getElem?_eq_getElem frameBound
    have position : frameIndex.val + depth.val + 1 = current.frames.val.length := by
      change current.frames.val.length - depth.val - 1 + depth.val + 1 = current.frames.val.length
      omega
    have room := held.room
    have codeFits : current.function.code.val.length + 2 ≤ Usize.max := by omega
    have sourceFits : current.function.source_offsets.val.length + 2 ≤ Usize.max := by
      rw [held.aligned]; exact codeFits
    have tableFits : current.function.jump_tables.val.length < Usize.max := by
      have := held.tables; omega
    obtain ⟨⟨result,next⟩,called,_⟩ := WP.spec_imp_exists
      (compiler_table_branch_total ops law current i frameIndex depth frame depthAt frameAt position
        tableFits (held.fixups.lookup frameAt (by omega)) codeFits sourceFits held.coordinate)
    apply WP.exists_imp_spec ⟨(result, next), called, ?_⟩
    intro accepted
    change result = .Ok () at accepted
    rw [accepted] at called
    exact held.advance ops law inside called
  · intro current index status safe finished
    trivial

end Itasca.Compiler

end

/-! ## Branch Table Lower Safety -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

@[step] theorem compiler_lower_table_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (aligned : SourceAligned compiler)
    (depths : ∀ depth ∈ compiler.table_depths.val, depth.val < compiler.frames.val.length)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (room : compiler.function.code.val.length + 1 + 2*compiler.table_depths.val.length ≤ Usize.max)
    (tables : compiler.function.jump_tables.val.length ≤ compiler.function.code.val.length)
    (coordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.lower_table_branches ops compiler ⦃ _ => True ⦄ := by
  apply runtime.compiler.control.FunctionCompiler.lower_table_branches.total ops law compiler
    (by omega) (by rw [aligned]; omega) coordinate
  intro start length selector emitted effect
  obtain ⟨budget,code,sources,rfl,codeEq,sourcesEq⟩ := effect.emitted
  have size : code.val.length = compiler.function.code.val.length+1 := by
    simp only [codeEq, List.length_append, List.length_singleton]
  have sourceSize : sources.val.length = compiler.function.source_offsets.val.length+1 := by
    have := congrArg List.length sourcesEq
    simpa only [List.length_map,List.length_append,List.length_singleton] using this
  let next := {compiler with budget,function := {compiler.function with code,source_offsets := sources}}
  have safe : TableLoopSafe next 0 Usize.max := by
    refine ⟨?_,depths,fixups.mono (by dsimp [next]; omega),?_,?_,coordinate⟩
    · change sources.val.length = code.val.length
      rw [sourceSize,size,aligned]
    · change code.val.length + 2*(compiler.table_depths.val.length-0) ≤ Usize.max
      simpa only [size,Nat.sub_zero] using room
    · change compiler.function.jump_tables.val.length ≤ code.val.length
      omega
  exact compiler_table_loop_total ops law next 0#usize (.Ok ()) Usize.max (Nat.le_refl _) (fun _ => safe)

end Itasca.Compiler

end

/-! ## Branch Table Callback Safety -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

@[step] theorem compiler_br_table_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (aligned : SourceAligned compiler)
    (depths : ∀ depth ∈ compiler.table_depths.val, depth.val < compiler.frames.val.length)
    (fallbackBound : fallback.val < compiler.frames.val.length)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (room : compiler.function.code.val.length + 1 + 2*(compiler.table_depths.val.length+1) ≤ Usize.max)
    (tables : compiler.function.jump_tables.val.length ≤ compiler.function.code.val.length)
    (coordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops compiler state fallback types ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  have normal : ∀ labeled,
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label ops compiler state fallback = .ok (.Ok (), labeled) →
      labeled.reachable = true → runtime.compiler.control.FunctionCompiler.lower_table_branches ops labeled ⦃ _ => True ⦄ := by
    intro labeled labelCall live
    obtain ⟨budget, labels, rfl, labelsEq⟩ := compiler_table_label_success ops law compiler labeled state fallback labelCall
    exact compiler_lower_table_total ops law {compiler with budget, table_depths := labels}
      aligned (by
        intro depth member
        rw [labelsEq] at member
        rcases List.mem_append.mp member with member | member
        · exact depths depth member
        · simp only [List.mem_singleton] at member
          subst depth
          exact fallbackBound)
      fixups (by simpa only [labelsEq, List.length_append, List.length_singleton] using room)
      tables coordinate
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table.total ops law compiler state fallback types (by omega) normal)
  rw [called, WP.spec_ok]
  intro accepted
  change status = .Ok () at accepted
  subst status
  obtain ⟨middle, observed⟩ := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table.inv
    ops compiler after state fallback types (.Ok ()) called).observation
  have stack := compiler_observe_stack ops law middle state
  rw [observed, WP.spec_ok] at stack
  exact stack rfl

end Itasca.Compiler

end

end
