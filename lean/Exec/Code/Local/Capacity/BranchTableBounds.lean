import Exec.Code.Local.Relations.Table.BranchTableBuild
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Each side-table entry is accompanied by at least one emitted instruction. -/
theorem TableTargetsBuilt.table_dominance {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depths targets : List U32}
    (built : TableTargetsBuilt before after depths targets)
    (bounded : before.function.jump_tables.val.length ≤ before.function.code.val.length) :
    after.function.jump_tables.val.length ≤ after.function.code.val.length := by
  induction built with
  | nil => exact bounded
  | cons _ _ _ appended _ _ effect rest ih =>
    apply ih
    obtain ⟨fragment,code,nonempty⟩ := effect.code_prefix
    simp only [appended,code,List.length_append,List.length_singleton]
    omega

/-- A selected side-table index is no larger than its actual bounded target PC.
This supplies U32 dispatch arithmetic even when vector lengths use Usize. -/
theorem TableTargetsBuilt.index_bound {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depths targets : List U32}
    (built : TableTargetsBuilt before after depths targets)
    (bounded : before.function.jump_tables.val.length ≤ before.function.code.val.length)
    (index : Nat) (entry : U32) (lookup : targets[index]? = some entry) :
    before.function.jump_tables.val.length + index ≤ entry.val := by
  induction built generalizing index entry with
  | nil => simp at lookup
  | @cons before middle after depths targets head target targetPC appended sameHeight sameDepths effect rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at lookup
      subst entry
      simpa only [Nat.add_zero,targetPC] using bounded
    | succ index =>
      have middleBound : middle.function.jump_tables.val.length ≤ middle.function.code.val.length := by
        obtain ⟨fragment,code,nonempty⟩ := effect.code_prefix
        simp only [appended,code,List.length_append,List.length_singleton]
        omega
      have bound := ih middleBound index entry lookup
      simpa only [appended,List.length_append,List.length_singleton,Nat.add_assoc,Nat.add_comm 1 index] using bound

theorem TableTargetsBuilt.dispatch_arithmetic {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depths : List U32} {fallback : U32} {targets : List U32}
    (built : TableTargetsBuilt before after (depths++[fallback]) targets)
    (bounded : before.function.jump_tables.val.length ≤ before.function.code.val.length) :
    before.function.jump_tables.val.length + depths.length ≤ U32.max := by
  have count := built.length
  have inside : depths.length < targets.length := by
    simp only [List.length_append,List.length_singleton] at count
    omega
  let entry := targets[depths.length]
  have bound := built.index_bound bounded depths.length entry (List.getElem?_eq_getElem inside)
  have entryMax : entry.val ≤ U32.max := by scalar_tac
  exact bound.trans entryMax
end Itasca.Runtime.Code
