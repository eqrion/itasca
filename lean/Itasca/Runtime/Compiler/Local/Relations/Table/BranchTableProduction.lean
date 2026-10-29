import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableBuild
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableLower
namespace Itasca.Runtime.Code
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
end Itasca.Runtime.Code
