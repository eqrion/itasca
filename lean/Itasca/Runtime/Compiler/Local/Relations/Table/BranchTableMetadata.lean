import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableTrace
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableSuccess
import Itasca.Runtime.Compiler.Local.Initializer.InitializerElementAppend
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Local.Relations.Table.ControlTablePreservation

/-!
Sections, each formerly its own module: BranchTableLower, BranchTableCallback, BranchTableMetadata.
-/

/-! ## BranchTableLower -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
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
  unfold runtime.compiler.control.FunctionCompiler.lower_table_branches at accepted
  obtain ⟨startResult,startCalled,rest⟩ := bind_ok_inv _ _ _ accepted
  cases startResult with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok start =>
    have startSpec := bounded_index (alloc.vec.Vec.len before.function.jump_tables)
    rw [startCalled, WP.spec_ok] at startSpec
    have startEq := startSpec start rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨lenResult,lenCalled,rest⟩ := bind_ok_inv _ _ _ rest
    cases lenResult with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok len =>
      have lenSpec := bounded_index (alloc.vec.Vec.len before.table_depths)
      rw [lenCalled, WP.spec_ok] at lenSpec
      have lenEq := lenSpec len rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨operand,operandCalled,rest⟩ := bind_ok_inv _ _ _ rest
      cases operand with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok selector =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨⟨emittedStatus,emitted⟩,emitCalled,rest⟩ := bind_ok_inv _ _ _ rest
        cases emittedStatus with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
        | Ok unit =>
          cases unit
          simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
          obtain ⟨output,loopCalled,rest⟩ := bind_ok_inv _ _ _ rest
          have statusEq : snapshotStatus output = .Ok () := by
            rcases output with ⟨signatures, functionSlots, budget, batchStart, function, frames, reachable,
              nextSource, operands, height, offsets, depths, status⟩
            exact (Prod.mk.inj (Result.ok.injEq.mp rest)).1
          have compilerEq : snapshotCompiler output = after := by
            rcases output with ⟨signatures, functionSlots, budget, batchStart, function, frames, reachable,
              nextSource, operands, height, offsets, depths, status⟩
            exact (Prod.mk.inj (Result.ok.injEq.mp rest)).2
          have trace := (compiler_table_loop_trace ops law emitted 0#usize (.Ok ()) output loopCalled statusEq).2
          rw [compilerEq] at trace
          exact ⟨start,len,selector,emitted,startEq,lenEq,operandCalled,
            compiler_emit_success ops law before emitted _ emitCalled,trace⟩
end Itasca.Runtime.Compiler

end

/-! ## BranchTableCallback -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Label collection changes only its buffer and allocation accounting. -/
theorem compiler_table_label_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
      ops before state depth = .ok (.Ok (),after)) :
    ∃ budget depths, after = {before with budget, table_depths := depths} ∧
      depths.val = before.table_depths.val ++ [depth] := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label at accepted
  obtain ⟨⟨result,budget⟩,_,rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok unit =>
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
    obtain ⟨⟨result,finalBudget,depths⟩,pushed,rest⟩ := bind_ok_inv _ _ _ rest
    simp only [uncurry_apply_pair,Result.ok.injEq,Prod.mk.injEq] at rest
    obtain ⟨rfl,rfl⟩ := rest
    exact ⟨finalBudget,depths,rfl,(budget_push_success ops law budget finalBudget before.table_depths depths depth pushed).2⟩

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
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table at accepted
  obtain ⟨⟨result,labeled⟩,labeledCall,rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok unit =>
    cases unit
    obtain ⟨budget,depths,rfl,depthEq⟩ := compiler_table_label_success ops law before labeled state default labeledCall
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,live,ite_true] at rest
    obtain ⟨⟨status,lowered⟩,lowerCalled,rest⟩ := bind_ok_inv _ _ _ rest
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unit =>
      cases unit
      simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
      obtain ⟨cleared,clearCalled,observeCalled⟩ := bind_ok_inv _ _ _ rest
      have empty := runtime_clear lowered.table_depths
      rw [clearCalled,WP.spec_ok] at empty
      exact ⟨budget,depths,lowered,cleared,depthEq,by simpa only [live] using lowerCalled,empty,observeCalled⟩
end Itasca.Runtime.Compiler

end

/-! ## BranchTableMetadata -/

section

namespace Itasca.Runtime.Compiler
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
end Itasca.Runtime.Compiler

end
