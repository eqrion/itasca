import Exec.Code.Local.Relations.Table.BranchTableCallbackProduction
namespace Exec.Code
open Aeneas Aeneas.Std

theorem TableTargetCode.code_growth {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depth : U32}
    (effect : TableTargetCode before after depth) :
    after.function.code.val.length ≤ before.function.code.val.length+2 := by
  cases effect with
  | loop index frame source lookup position kind operands code frames =>
    rw [code,List.length_append]
    simp only [branchInstructions]
    split <;> simp
  | forward index frame source fixups site lookup position kind operands code frames appended sitePosition =>
    rw [code,List.length_append]
    simp only [branchInstructions]
    split <;> simp

theorem TableTargetsBuilt.code_growth {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depths targets : List U32}
    (built : TableTargetsBuilt before after depths targets) :
    after.function.code.val.length ≤ before.function.code.val.length+2*depths.length := by
  induction built with
  | nil => simp
  | cons _ _ _ _ _ _ effect rest ih =>
    have bound := effect.code_growth
    simp only [List.length_cons]
    omega

/-- One dispatch header and at most one copy plus one jump per target. -/
theorem compiler_br_table_code_growth {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (live : before.reachable=true)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types=.ok (.Ok (),after)) :
    after.function.code.val.length ≤ before.function.code.val.length+1+2*(before.table_depths.val.length+1) := by
  obtain ⟨budget,depths,start,len,selector,emitted,lowered,targets,_,_,_,emission,built,code,_,_,_,_,_,_⟩ :=
    compiler_br_table_production ops law before after state fallback types live accepted
  have growth := built.code_growth
  obtain ⟨_,newCode,_,emittedEq,codeEq,_⟩ := emission
  rw [emittedEq] at growth
  simpa only [code,codeEq,List.length_append,List.length_singleton] using growth
end Exec.Code
