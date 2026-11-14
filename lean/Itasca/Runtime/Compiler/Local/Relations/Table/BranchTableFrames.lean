import Itasca.Runtime.Compiler.Local.Callbacks.Control.BranchTableCallbacks
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableBuild
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableTrace
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseScope

/-!
Sections, each formerly its own module: BranchTableProduction, BranchTableCallbackProduction, BranchTableDead, BranchTableFrames.
-/

/-! ## BranchTableProduction -/

section

namespace Itasca.Runtime.Compiler
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
end Itasca.Runtime.Compiler

end

/-! ## BranchTableCallbackProduction -/

section

namespace Itasca.Runtime.Compiler
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
end Itasca.Runtime.Compiler

end

/-! ## BranchTableDead -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
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
    have empty := runtime_clear labeled.table_depths
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

end Itasca.Runtime.Compiler

end

/-! ## BranchTableFrames -/

section

namespace Itasca.Runtime.Compiler
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
end Itasca.Runtime.Compiler

end
