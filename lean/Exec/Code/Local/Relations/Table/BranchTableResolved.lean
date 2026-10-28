import Exec.Code.Local.Relations.Table.BranchTableResolution
import Exec.Code.Local.Relations.Table.BranchTableOperands
import Exec.Code.Local.Relations.Table.BranchTableLayout
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
