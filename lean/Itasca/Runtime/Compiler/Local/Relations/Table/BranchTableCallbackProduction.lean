import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableProduction
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableCallback
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
