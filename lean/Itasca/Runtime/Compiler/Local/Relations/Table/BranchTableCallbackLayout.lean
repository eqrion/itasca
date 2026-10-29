import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableSites
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableOperands
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableLayout
import Itasca.Runtime.Compiler.Local.Capacity.BranchTableBounds
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableProduction
import Itasca.Runtime.Compiler.Local.Lowering.Local.LoweringLocal
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableCallback
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableBoundary

/-!
Resolved br_table target layouts and their callback certificate. Per-target resolution composes into the built table and final source prefix.
-/

/-! ## Branch Table Resolution -/

section

namespace Itasca.Runtime.Code
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
    · rw [code,resolvedCode_append_code _ _ _ (prior.inside sites),future.loopTarget kind]
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
      exact resolvedCode_new_br before.function.code.val earlier later ⟨frame.fixups.val,label.target⟩
        frame.height source frame.results core.num.U32.MAX site sitePosition (prior.inside sites)
end Itasca.Runtime.Code

end

/-! ## Branch Table Resolved -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
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
    have labelShape := scopeLabels_lookup labelShapes scopeAt labelAt
    have layout := table_operand_layout shape labelShape entered input source before.height height sourceEq
    let fragment := branchInstructions frame.height source (frameBranchWidth frame) label.target
    have resolved : resolvedCode after.function.code.val groups =
        resolvedCode before.function.code.val previous ++ (fragment++tailCode) := by
      rw [tailResolved,armResolved,List.append_assoc]
    have lengthArm : middle.function.code.val.length =
        before.function.code.val.length+fragment.length := by
      have equation := congrArg List.length armResolved
      simpa only [resolvedCode_length,List.length_append] using equation
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
        · simpa only [resolvedCode_length] using targetPC.symm
        · simpa only [targetPC,fragment] using lengthArm
      · simp only [resolvedCode_length]
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
end Itasca.Runtime.Code

end

/-! ## Branch Table Layout Production -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
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
    rw [codeEq,resolvedCode_append_code _ _ _ (priorPlans.inside sites)]
  have dispatch : (resolvedCode after.function.code.val groups)[before.function.code.val.length]? =
      some (.JumpTable selector start len) := by
    rw [resolved,headerResolved,List.append_assoc]
    simp [List.getElem?_append,resolvedCode_length]
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
end Itasca.Runtime.Code

end

/-! ## Branch Table Callback Layout -/

section

namespace Itasca.Runtime.Code
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
end Itasca.Runtime.Code

end
