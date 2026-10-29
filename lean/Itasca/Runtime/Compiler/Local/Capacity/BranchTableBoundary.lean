import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableCallbackProduction
import Itasca.Runtime.Compiler.Local.Capacity.BranchTableBounds
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableDead
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Actual successful table callbacks restore the raw compiler boundary before
any future relocation plan is chosen. -/
theorem compiler_br_table_boundary {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (dominance : before.function.jump_tables.val.length≤before.function.code.val.length)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types=.ok (.Ok (),after)) :
    CompilerTableBoundary after ∧ after.reachable=false := by
  by_cases live : before.reachable=true
  · obtain ⟨budget,depths,start,len,selector,emitted,lowered,targets,_,_,_,emission,built,
      codeAfter,_,tablesAfter,_,cleared,dead,_⟩ := compiler_br_table_production ops law before after state fallback types live accepted
    obtain ⟨emitBudget,newCode,newSources,emittedEq,codeEq,_⟩ := emission
    have emittedBound : emitted.function.jump_tables.val.length≤emitted.function.code.val.length := by
      rw [emittedEq]
      simp only [codeEq,List.length_append,List.length_singleton]
      omega
    have bounded := built.table_dominance emittedBound
    have tables := built.tables
    rw [emittedEq] at tables
    refine ⟨⟨cleared,?_⟩,dead⟩
    rw [codeAfter,tablesAfter,←tables]
    exact bounded
  · have dead : before.reachable=false := by cases same : before.reachable <;> simp_all
    obtain ⟨_,code,tables,_,cleared,afterDead,_,_⟩ := compiler_br_table_dead_effect ops law before after state fallback types dead accepted
    exact ⟨⟨cleared,by simpa only [code,tables] using dominance⟩,afterDead⟩
end Itasca.Runtime.Compiler
