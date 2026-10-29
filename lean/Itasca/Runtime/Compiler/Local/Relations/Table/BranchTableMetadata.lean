import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableCallback
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerBranchMetadata
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchSuccessControls
import Itasca.Runtime.Compiler.Local.Relations.Table.ControlTablePreservation
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
