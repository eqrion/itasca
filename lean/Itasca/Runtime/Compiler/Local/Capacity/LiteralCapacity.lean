import Itasca.Runtime.Compiler.Local.Callbacks.CallbackEquations
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableBuild
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableFrames
import Itasca.Binary.Wasm1.EncodingComplete
import Itasca.Runtime.Compiler.Local.Capacity.ControlCapacity

/-!
Sections, each formerly its own module: BranchTableBounds, BranchTableBoundary, BranchTableGrowth, BranchTableSourceGrowth, LiteralCapacity.
-/

/-! ## BranchTableBounds -/

section

namespace Itasca.Runtime.Compiler
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
end Itasca.Runtime.Compiler

end

/-! ## BranchTableBoundary -/

section

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

end

/-! ## BranchTableGrowth -/

section

namespace Itasca.Runtime.Compiler
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
end Itasca.Runtime.Compiler

end

/-! ## BranchTableSourceGrowth -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Each accepted label consumes at least one source byte, including nonminimal
LEB encodings. -/
theorem table_labels_byte_bound {data start depths next}
    (decoded : BrTable.LabelsDecoded data start depths next) :
    start.val+depths.length≤next.val := by
  induction decoded with
  | nil => simp
  | snoc prior label ih =>
    have consumed := label.span
    simp only [List.length_append,List.length_singleton]
    omega

theorem table_immediate_byte_bound {data start depths fallback next}
    (decoded : BrTable.Decoded data start depths fallback next) :
    start.val+depths.length+2≤next.val := by
  obtain ⟨count,first,last,countDecoded,_,labels,defaultDecoded⟩ := decoded
  have countBytes := countDecoded.span
  have labelsBytes := table_labels_byte_bound labels
  have defaultBytes := defaultDecoded.span
  omega

end Itasca.Runtime.Compiler

end

/-! ## LiteralCapacity -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
theorem compiler_op65_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 65#u16 a b bits = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  by_cases reach : before.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.i32_const ops before state a b bits reach
    rw [run] at accepted
    repeat' capacity_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact ⟨(compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).1,
      (compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).2 rfl⟩

theorem compiler_op66_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 66#u16 a b bits = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  by_cases reach : before.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.i64_const ops before state a b bits reach
    rw [run] at accepted
    repeat' capacity_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact ⟨(compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).1,
      (compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).2 rfl⟩

theorem compiler_op32_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 32#u16 a b bits = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  by_cases reach : before.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.local_get ops before state a b bits reach
    rw [run] at accepted
    repeat' capacity_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact ⟨(compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).1,
      (compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).2 rfl⟩

theorem compiler_op33_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 33#u16 a b bits = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  by_cases reach : before.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.local_set ops before state a b bits reach
    rw [run] at accepted
    repeat' capacity_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact ⟨(compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).1,
      (compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).2 rfl⟩

theorem compiler_op34_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 34#u16 a b bits = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  by_cases reach : before.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.local_tee ops before state a b bits reach
    rw [run] at accepted
    repeat' capacity_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact ⟨(compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).1,
      (compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).2 rfl⟩

theorem compiler_op16_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 16#u16 a b bits = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  by_cases reach : before.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.call ops before state a b bits reach
    rw [run] at accepted
    repeat' capacity_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact ⟨(compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).1,
      (compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).2 rfl⟩

theorem compiler_op1_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 1#u16 a b bits = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  by_cases reach : before.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.nop ops before state a b bits reach
    rw [run] at accepted
    repeat' capacity_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact ⟨(compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).1,
      (compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).2 rfl⟩

theorem compiler_op26_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 26#u16 a b bits = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  by_cases reach : before.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.drop ops before state a b bits reach
    rw [run] at accepted
    repeat' capacity_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact ⟨(compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).1,
      (compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).2 rfl⟩

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_i32_const_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : I32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const
      ops before state value = .ok (.Ok (), after)) : CapacityStep before after state := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const.eq] at accepted
  simp only [lift, bind_ok] at accepted
  exact compiler_op65_capacity ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_i64_const_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : I64)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const
      ops before state value = .ok (.Ok (), after)) : CapacityStep before after state := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const.eq] at accepted
  simp only [lift, bind_ok] at accepted
  exact compiler_op66_capacity ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_local_get_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_get
      ops before state value = .ok (.Ok (), after)) : CapacityStep before after state := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_get.eq] at accepted
  exact compiler_op32_capacity ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_local_set_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_set
      ops before state value = .ok (.Ok (), after)) : CapacityStep before after state := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_set.eq] at accepted
  exact compiler_op33_capacity ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_local_tee_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_tee
      ops before state value = .ok (.Ok (), after)) : CapacityStep before after state := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_tee.eq] at accepted
  exact compiler_op34_capacity ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_call_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_call
      ops before state value = .ok (.Ok (), after)) : CapacityStep before after state := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_call.eq] at accepted
  exact compiler_op16_capacity ops law before after state _ _ _ accepted

theorem compiler_nop_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_nop
      ops before state = .ok (.Ok (), after)) : CapacityStep before after state := by
  exact compiler_op1_capacity ops law before after state _ _ _ accepted

theorem compiler_drop_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (dropped : Itasca.code.StackType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_drop
      ops before state dropped = .ok (.Ok (), after)) : CapacityStep before after state := by
  exact compiler_op26_capacity ops law before after state _ _ _ accepted


end Itasca.Runtime.Compiler

end
