import Itasca.Runtime.Code.Local.Relations.Table.BranchTableResolved
import Itasca.Runtime.Code.Local.Capacity.BranchTableBounds
import Itasca.Runtime.Code.Local.Relations.Table.BranchTableProduction
import Itasca.Runtime.Code.Local.Lowering.Local.LoweringLocal
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
