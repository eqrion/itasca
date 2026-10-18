import Exec.Code.Local.Relations.Table.BranchTableBuild
namespace Exec.Code
open Aeneas Aeneas.Std

/-- Every final dispatch-table entry points to its actual ordered branch arm.
The arm's exact code remains a prior-contained fragment of the completed code. -/
theorem TableTargetsBuilt.selected {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depths targets : List U32}
    (built : TableTargetsBuilt before after depths targets)
    (index : Nat) (depth : U32) (lookup : depths[index]? = some depth) :
    ∃ (entry : U32) (armBefore armAfter : runtime.compiler.FunctionCompiler A)
      (prior suffix : List Bytecode),
      after.function.jump_tables.val[before.function.jump_tables.val.length+index]? = some entry ∧
      entry.val = armBefore.function.code.val.length ∧
      armBefore.function.code.val = before.function.code.val ++ prior ∧
      after.function.code.val = armAfter.function.code.val ++ suffix ∧
      TableTargetCode armBefore armAfter depth ∧
      entry.val < after.function.code.val.length := by
  induction built generalizing index depth with
  | nil => simp at lookup
  | @cons before middle after depths targets head target pc appended height same effect rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at lookup
      subst depth
      obtain ⟨suffix,afterCode,_⟩ := rest.code_prefix
      obtain ⟨fragment,armCode,nonempty⟩ := effect.code_prefix
      have entryBound : target.val < after.function.code.val.length := by
        rw [afterCode,armCode]
        simp only [List.length_append]
        omega
      refine ⟨target,before,middle,[],suffix,?_,pc,by simp,afterCode,effect,entryBound⟩
      rw [rest.tables,appended,List.append_assoc]
      simp
    | succ index =>
      simp only [List.getElem?_cons_succ] at lookup
      obtain ⟨entry,armBefore,armAfter,prior,suffix,entryLookup,entryPC,armCode,afterCode,armEffect,entryBound⟩ :=
        ih index depth lookup
      obtain ⟨first,firstCode,_⟩ := effect.code_prefix
      refine ⟨entry,armBefore,armAfter,first++prior,suffix,?_,entryPC,?_,afterCode,armEffect,entryBound⟩
      · simpa only [appended,List.length_append,List.length_singleton,Nat.add_assoc,Nat.add_comm 1 index] using entryLookup
      · rw [armCode,firstCode,List.append_assoc]
end Exec.Code
