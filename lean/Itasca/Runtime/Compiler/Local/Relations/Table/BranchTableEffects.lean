import Itasca.Runtime.Compiler.Local.Capacity.BranchTableBoundary
import Itasca.Runtime.Compiler.Local.Capacity.BranchTableSourceGrowth
namespace Itasca.Runtime.Compiler
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
end Itasca.Runtime.Compiler
