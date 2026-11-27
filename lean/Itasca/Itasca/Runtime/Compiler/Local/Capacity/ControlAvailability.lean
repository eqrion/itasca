import Itasca.Runtime.Compiler.Local.Callbacks.CallbackEquations
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableFrames
import Itasca.Binary.Scalar.Encoding
import Itasca.Runtime.Compiler.Local.Capacity.ControlCapacity
import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchContracts
import Itasca.Runtime.Compiler.Local.Capacity.CallbackBudgets
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CallbackRetention
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeFrames
import Itasca.Runtime.Compiler.Local.Lowering.LoweringLocal
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ClosingContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Function.FunctionStartContracts
import Itasca.Runtime.Compiler.Local.Relations.Local.LocalDeclarations
import Itasca.Runtime.Compiler.Local.Initializer.ModuleMappings
import Itasca.Runtime.Compiler.Local.Capacity.IndependentBodyReplay
import Itasca.Runtime.Compiler.Local.Relations.Global.GlobalLowering

open WebAssembly

/-!
Proofs for Runtime / Compiler / Local / Capacity.

This module collects BranchTableAndLiteralCapacity, ControlAvailability, EntryAndBranchCapacity.
Each section documents its contracts and consumers.
-/

/-! ## BranchTableAndLiteralCapacity -/

section

/-!
# Branch Table And Literal Capacity

Branch-table sizes and literal emission demands are bounded by the retained compiler capacity premises.
-/

/-! ## BranchTableBounds -/

section

namespace Itasca.Compiler
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
end Itasca.Compiler

end

/-! ## BranchTableBoundary -/

section

namespace Itasca.Compiler
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
end Itasca.Compiler

end

/-! ## BranchTableGrowth -/

section

namespace Itasca.Compiler
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
end Itasca.Compiler

end

/-! ## BranchTableSourceGrowth -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Each accepted label consumes at least one source byte, including nonminimal
LEB encodings. -/
theorem table_labels_byte_bound {data start depths next}
    (decoded : Body.BrTable.LabelsDecoded data start depths next) :
    start.val+depths.length≤next.val := by
  induction decoded with
  | nil => simp
  | snoc prior label ih =>
    have consumed := label.span
    simp only [List.length_append,List.length_singleton]
    omega

theorem table_immediate_byte_bound {data start depths fallback next}
    (decoded : Body.BrTable.Decoded data start depths fallback next) :
    start.val+depths.length+2≤next.val := by
  obtain ⟨count,first,last,countDecoded,_,labels,defaultDecoded⟩ := decoded
  have countBytes := countDecoded.span
  have labelsBytes := table_labels_byte_bound labels
  have defaultBytes := defaultDecoded.span
  omega

end Itasca.Compiler

end

/-! ## LiteralCapacity -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation
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

end Itasca.Compiler

end

end

/-! ## ControlAvailability -/

section

open Itasca.Representation

/-!
# Control Availability

END and other control callbacks return normally when their code, scope and fixup resources are available.
-/

/-! ## EndDispatchAvailability -/

section

/-!
Availability of end callbacks for root bodies, ordinary scopes and guarded scopes. The dispatch proof retains each scope-specific allocation obligation.
-/

/-! ## Close Body Availability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Root closing accepts from retained branch-hole shapes and map ownership.
The implicit epilogue consumes one instruction, including for dead bodies. -/
theorem compiler_close_body_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (demand : CallbackDemand compiler state bound)
    (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (kind : frame.kind = .Body) (noIf : frame.if_pc = none)
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Body .Empty ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  have guardSites : ∀ guard, frame.if_pc = some guard →
      ∃ branch old, compiler.function.code.val[guard.val]? = some (BranchKind.instruction branch old) := by
    intro guard h
    rw [noIf] at h
    contradiction
  have pcFits : compiler.function.code.length ≤ U32.max := by
    scalar_tac
  have space : frame.kind = .Body → compiler.function.code.length < Usize.max ∧
      compiler.function.source_offsets.length < Usize.max ∧
      compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max ∧
      compiler.function.code.length + 1 ≤ bound ∧ compiler.function.source_offsets.length + 1 ≤ bound ∧
      compiler.budget.instructions.val < compiler.budget.limits.max_instructions.val := by
    intro _
    exact ⟨demand.codeCapacity, demand.sourceCapacity, demand.coordinate, demand.codeReserve,
      demand.sourceReserve, demand.instruction⟩
  apply WP.spec_mono (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end.available
    ops bound available compiler state .Body .Empty
    ⟨frame, rest, frames, branches, guardSites, mapFits, coordinateFits, pcFits,
      demand.operands, demand.slots, space⟩)
  intro out post
  rcases out with ⟨status, after⟩
  rcases post with ⟨statusOk, used, budgetEq, usedEq⟩
  subst status
  have usedEqOne : used.val = compiler.budget.instructions.val + 1 := by
    simpa [kind] using usedEq
  refine ⟨rfl, ?_⟩
  rw [budgetEq]
  exact CompilationBudgetEffect.of_counter .instructions compiler.budget used 1
    (by simp [ChargeCounter.used] at usedEqOne ⊢; omega)
    (by simp [ChargeCounter.used] at usedEqOne ⊢; omega)

end Itasca.Compiler

end

/-! ## Guarded Scope Close Availability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Non-root scope closing accepts from retained holes, map ownership, and
independent observer demand, preserving every compiler resource counter. -/
theorem compiler_close_guarded_scope_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (guard : Usize) (condition old : U32)
    (nonBody : frame.kind ≠ .Body) (hasIf : frame.if_pc = some guard)
    (guardCode : compiler.function.code.val[guard.val]? = some (.JumpIfZero condition old))
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max)
    (request : state.vals.length ≤ bound)
    (slotsFit : compiler.function.local_slots.val + 2*state.vals.length ≤ U32.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty ⦃ out =>
      out.1 = .Ok () ∧ out.2.budget = compiler.budget ⦄ := by
  have guardSites : ∀ guard, frame.if_pc = some guard →
      ∃ branch old, compiler.function.code.val[guard.val]? = some (BranchKind.instruction branch old) := by
    intro queried h
    have same : queried = guard := Option.some.inj (h.symm.trans hasIf)
    subst queried
    exact ⟨.zero condition, old, by simpa [BranchKind.instruction] using guardCode⟩
  have pcFits : compiler.function.code.length ≤ U32.max := by
    scalar_tac
  have space : frame.kind = .Body → compiler.function.code.length < Usize.max ∧
      compiler.function.source_offsets.length < Usize.max ∧
      compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max ∧
      compiler.function.code.length + 1 ≤ bound ∧ compiler.function.source_offsets.length + 1 ≤ bound ∧
      compiler.budget.instructions.val < compiler.budget.limits.max_instructions.val := by
    intro body
    exact False.elim (nonBody body)
  apply WP.spec_mono (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end.available
    ops bound available compiler state .Block .Empty
    ⟨frame, rest, frames, branches, guardSites, mapFits, coordinateFits, pcFits, request, slotsFit, space⟩)
  intro out post
  rcases out with ⟨status, after⟩
  rcases post with ⟨statusOk, used, budgetEq, usedEq⟩
  subst status
  have countZero : (match frame.kind with | .Body => 1 | _ => 0) = 0 := by
    cases kindEq : frame.kind <;> simp_all
  have usedEqOld : used.val = compiler.budget.instructions.val := by
    simpa [countZero] using usedEq
  have usedSame : used = compiler.budget.instructions := by
    apply UScalar.eq_of_val_eq
    exact usedEqOld
  rw [budgetEq, usedSame]
  exact ⟨rfl, rfl⟩

end Itasca.Compiler

end

/-! ## Scope Close Availability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Non-root scope closing accepts from retained holes, map ownership, and
independent observer demand, preserving every compiler resource counter. -/
theorem compiler_close_scope_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (nonBody : frame.kind ≠ .Body) (noIf : frame.if_pc = none)
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max)
    (request : state.vals.length ≤ bound)
    (slotsFit : compiler.function.local_slots.val + 2*state.vals.length ≤ U32.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty ⦃ out =>
      out.1 = .Ok () ∧ out.2.budget = compiler.budget ⦄ := by
  have guardSites : ∀ guard, frame.if_pc = some guard →
      ∃ branch old, compiler.function.code.val[guard.val]? = some (BranchKind.instruction branch old) := by
    intro guard h
    rw [noIf] at h
    contradiction
  have pcFits : compiler.function.code.length ≤ U32.max := by
    scalar_tac
  have space : frame.kind = .Body → compiler.function.code.length < Usize.max ∧
      compiler.function.source_offsets.length < Usize.max ∧
      compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max ∧
      compiler.function.code.length + 1 ≤ bound ∧ compiler.function.source_offsets.length + 1 ≤ bound ∧
      compiler.budget.instructions.val < compiler.budget.limits.max_instructions.val := by
    intro body
    exact False.elim (nonBody body)
  apply WP.spec_mono (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end.available
    ops bound available compiler state .Block .Empty
    ⟨frame, rest, frames, branches, guardSites, mapFits, coordinateFits, pcFits, request, slotsFit, space⟩)
  intro out post
  rcases out with ⟨status, after⟩
  rcases post with ⟨statusOk, used, budgetEq, usedEq⟩
  subst status
  have countZero : (match frame.kind with | .Body => 1 | _ => 0) = 0 := by
    cases kindEq : frame.kind <;> simp_all
  have usedEqOld : used.val = compiler.budget.instructions.val := by
    simpa [countZero] using usedEq
  have usedSame : used = compiler.budget.instructions := by
    apply UScalar.eq_of_val_eq
    exact usedEqOld
  rw [budgetEq, usedSame]
  exact ⟨rfl, rfl⟩

end Itasca.Compiler

end

/-! ## End Dispatch Availability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Every end callback accepts from retained scope ownership and independent
capacity, including the nonvoid dead-body epilogue. Target PCs are constructed
from numeric bounds; source guard/fixup shapes discharge actual patching. -/
theorem compiler_end_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 1)
    (frame : runtime.compiler.Frame) (rest : alloc.vec.Vec runtime.compiler.Frame)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (rootNoGuard : frame.kind = .Body → frame.if_pc = none)
    (guardOwned : ∀ guard, frame.if_pc = some guard → ∃ condition old,
      compiler.function.code.val[guard.val]? = some (.JumpIfZero condition old))
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  have fits : compiler.function.code.length < 2^UScalarTy.U32.numBits := by
    have room := capacity.pc
    scalar_tac
  let target := U32.ofNatCore compiler.function.code.length fits
  have position : target.val = compiler.function.code.val.length := U32.ofNatCore_val_eq fits
  by_cases root : frame.kind = .Body
  · exact compiler_close_body_available ops bound available compiler state (capacity.one (by decide))
      frame rest target frames root (rootNoGuard root) position branches mapFits coordinateFits
  · cases guardPc : frame.if_pc with
    | none =>
      apply WP.spec_mono (compiler_close_scope_available ops bound available compiler state frame rest target frames root
        guardPc position branches mapFits coordinateFits capacity.operands capacity.slots)
      intro out post
      rw [post.2]
      exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩
    | some guard =>
      obtain ⟨condition,old,guardCode⟩ := guardOwned guard guardPc
      apply WP.spec_mono (compiler_close_guarded_scope_available ops bound available compiler state frame rest target frames
        guard condition old root guardPc guardCode position branches mapFits coordinateFits capacity.operands capacity.slots)
      intro out post
      rw [post.2]
      exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Compiler

end

end

/-! ## EnterAvailability -/

section

/-!
Allocation availability for scope publication and entry without emitted code. The publication reserve is discharged before constructing the entered compiler state.
-/

/-! ## Enter Availability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Exact entry counters imply the independent compilation budget bounds. -/
theorem EnterBudget.compilation_effect {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (kind : code.LabelKind) (effect : EnterBudget before after kind) :
    CompilationBudgetEffect before.budget after.budget (fun counter =>
      match counter with
      | .instructions => enterInstructionCharge before.reachable kind
      | .controls => 1
      | _ => 0) := by
  obtain ⟨instructions, controls, same, instructionsEq, controlsEq⟩ := effect
  rw [same]
  refine ⟨rfl, rfl, ?_⟩
  intro counter
  cases counter <;> simp only [ChargeCounter.used] <;> constructor <;> omega

/-- Opening an ordinary block or a dead scope accepts without emitting code.
Its budget effect is exactly one control, with all other counters retained. -/
theorem compiler_enter_without_emission_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : ScopeDemand compiler state bound) (ctrl : Itasca.code.Ctrl)
    (prior : List Itasca.code.Ctrl) (kind : Itasca.code.LabelKind)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (noThen : compiler.reachable = true → kind ≠ .Then)
    (noLoop : compiler.reachable = true → kind ≠ .Loop) :
    runtime.compiler.control.FunctionCompiler.enter ops compiler state kind bt ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .controls then 1 else 0) ⦄ := by
  clear heightFits -- The scope demand supplies the stronger whole-stack bound.
  refine WP.spec_mono (runtime.compiler.control.FunctionCompiler.enter.available ops bound available compiler state kind bt
    ⟨prior, ctrl, signature, controls, selected, valuesFit⟩ ?_ ?_) ?_
  · refine ⟨demand.pc, ?_, demand.coordinate, demand.mapsCapacity, demand.mapsReserve,
      demand.framesCapacity, demand.framesReserve, demand.control, demand.operands, demand.slots, ?_⟩
    · intro live thenKind
      exact False.elim (noThen live thenKind)
    · intro live emitted
      rcases emitted with thenKind | loopKind
      · exact False.elim (noThen live thenKind)
      · exact False.elim (noLoop live loopKind)
  · intro live thenKind
    exact False.elim (noThen live thenKind)
  · intro out post
    refine ⟨post.1, (EnterBudget.compilation_effect compiler out.2 kind post.2).weaken ?_⟩
    have zero : enterInstructionCharge compiler.reachable kind = 0 := by
      cases active : compiler.reachable with
      | false => simp [enterInstructionCharge]
      | true => cases kind <;> simp_all [enterInstructionCharge]
    intro counter
    cases counter <;> simp [zero]

end Itasca.Compiler

end

end

/-! ## ScopeAvailability -/

section

/-!
Availability of block, loop and if entry callbacks under source stack bounds. The common theorem retains the branch-specific allocation premises.
-/

/-! ## Enter If Availability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Live if opening accepts with one instruction and one control charge.
All control-map and frame storage is independently bounded. -/
theorem compiler_enter_if_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (scope : ScopeDemand compiler state bound)
    (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (pcRoom : compiler.function.code.length + 1 ≤ U32.max)
    (front : List valtype) (layout : CompilerLayout compiler (front ++ [.I32]))
    (live : compiler.reachable = true) :
    runtime.compiler.control.FunctionCompiler.enter ops compiler state .Then bt ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0) ⦄ := by
  clear heightFits -- The scope demand supplies the stronger whole-stack bound.
  refine WP.spec_mono (runtime.compiler.control.FunctionCompiler.enter.available ops bound available compiler state .Then bt
    ⟨prior, ctrl, signature, controls, selected, valuesFit⟩ ?_ ?_) ?_
  · exact ⟨scope.pc, fun _ _ => pcRoom, scope.coordinate, scope.mapsCapacity, scope.mapsReserve,
      scope.framesCapacity, scope.framesReserve, scope.control, scope.operands, scope.slots,
      fun _ _ => ⟨demand.codeCapacity, demand.sourceCapacity, demand.codeReserve,
        demand.sourceReserve, demand.instruction⟩⟩
  · intro _ _
    obtain ⟨condition, called, _⟩ := last_operand ops compiler front .I32 layout
    exact ⟨condition, called⟩
  · intro out post
    refine ⟨post.1, (EnterBudget.compilation_effect compiler out.2 .Then post.2).weaken ?_⟩
    intro counter
    cases counter <;> simp [enterInstructionCharge, live]

end Itasca.Compiler

end

/-! ## Enter Loop Availability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Live loop opening accepts with one instruction and one control charge.
All control-map and frame storage is independently bounded. -/
theorem compiler_enter_loop_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (scope : ScopeDemand compiler state bound)
    (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (pcRoom : compiler.function.code.length + 1 ≤ U32.max)
    (live : compiler.reachable = true) :
    runtime.compiler.control.FunctionCompiler.enter ops compiler state .Loop bt ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0) ⦄ := by
  clear heightFits -- The scope demand supplies the stronger whole-stack bound.
  refine WP.spec_mono (runtime.compiler.control.FunctionCompiler.enter.available ops bound available compiler state .Loop bt
    ⟨prior, ctrl, signature, controls, selected, valuesFit⟩ ?_ ?_) ?_
  · exact ⟨scope.pc, fun _ _ => pcRoom, scope.coordinate, scope.mapsCapacity, scope.mapsReserve,
      scope.framesCapacity, scope.framesReserve, scope.control, scope.operands, scope.slots,
      fun _ _ => ⟨demand.codeCapacity, demand.sourceCapacity, demand.codeReserve,
        demand.sourceReserve, demand.instruction⟩⟩
  · intro _ impossible
    cases impossible
  · intro out post
    refine ⟨post.1, (EnterBudget.compilation_effect compiler out.2 .Loop post.2).weaken ?_⟩
    intro counter
    cases counter <;> simp [enterInstructionCharge, live]

end Itasca.Compiler

end

/-! ## Scope Availability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- All scope kinds accept under source control/signature information and
independent demands. Live if entry alone needs a condition layout; dead code
requires no live operand layout. Scope height arithmetic follows from the
same conservative slot bound used by ordinary callbacks. -/
theorem compiler_enter_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (scope : ScopeDemand compiler state bound)
    (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl) (kind : Itasca.code.LabelKind)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (pcRoom : compiler.function.code.length + 1 ≤ U32.max)
    (conditionLayout : compiler.reachable = true → kind = .Then →
      ∃ front, CompilerLayout compiler (front ++ [.I32])) :
    runtime.compiler.control.FunctionCompiler.enter ops compiler state kind bt ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0) ⦄ := by
  have heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max := by
    have words := stack_words_le_twice_length (state.vals.val.take ctrl.value_stack_base.val)
    have lengthBound : (state.vals.val.take ctrl.value_stack_base.val).length ≤ state.vals.val.length := by
      simp only [List.length_take]; exact Nat.min_le_right _ _
    have room := scope.slots
    simp only [alloc.vec.Vec.length] at room
    omega
  by_cases loopEntry : compiler.reachable = true ∧ kind = .Loop
  · obtain ⟨live,rfl⟩ := loopEntry
    exact compiler_enter_loop_available ops bound available compiler state demand scope ctrl prior bt signature
      controls selected valuesFit heightFits pcRoom live
  · by_cases ifEntry : compiler.reachable = true ∧ kind = .Then
    · obtain ⟨live,rfl⟩ := ifEntry
      obtain ⟨front,layout⟩ := conditionLayout live rfl
      exact compiler_enter_if_available ops bound available compiler state demand scope ctrl prior bt signature
        controls selected valuesFit heightFits pcRoom front layout live
    · apply WP.spec_mono (compiler_enter_without_emission_available ops bound available compiler state scope ctrl prior
        kind bt signature controls selected valuesFit heightFits
        (by intro live same; exact ifEntry ⟨live,same⟩)
        (by intro live same; exact loopEntry ⟨live,same⟩))
      intro out post
      exact ⟨post.1,post.2.weaken (by intro counter; cases counter <;> simp)⟩

end Itasca.Compiler

end

end

/-! ## ReturnAvailability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Return accepts from a retained root frame and a source-justified result
width. Dead returns need neither a live root lookup nor result operands. -/
theorem compiler_return_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (body : runtime.compiler.Frame)
    (bodyFrame : compiler.reachable = true → compiler.frames.val[0]? = some body)
    (height : compiler.reachable = true → body.results.val ≤ compiler.height.val) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops compiler state ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  apply WP.spec_mono (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return.available ops bound available compiler state demand body bodyFrame height)
  rintro ⟨status, after⟩ ⟨accepted, used, frame, usedEq⟩
  dsimp only at frame usedEq ⊢
  rw [frame]
  refine ⟨accepted, .of_counter .instructions compiler.budget used 1 ?_ ?_⟩
  · simp only [ChargeCounter.used]
    split at usedEq <;> scalar_tac
  · simp only [ChargeCounter.used]
    split at usedEq <;> scalar_tac

end Itasca.Compiler

end

end

/-! ## EntryAndBranchCapacity -/

section

open Itasca.Representation

/-!
# Entry And Branch Capacity

Function entry and branch callbacks preserve the capacity invariants for emitted code and auxiliary tables.
-/

/-! ## FunctionStartAvailability -/

section

/-!
Availability of function start, from a single local allocation through the local-declaration loop. FunctionStartDemand records the bounds consumed by the entry construction.
-/

/-! ## Function Start Availability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- The actual function-start callback accepts under independent signature,
coordinate, and resource bounds. It changes precisely the local and root-control
budget counters, preserving every other budget field. -/
theorem compiler_function_start_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (ctx : Itasca.code.Context)
    (typeIndex : U32) (signature : runtime.compiler.Signature) (bodyBegin bodyEnd : Usize)
    (lookup : compiler.signatures.val[typeIndex.val]? = some signature)
    (beginFits : compiler.batch_start.val+bodyBegin.val ≤ Usize.max)
    (endFits : compiler.batch_start.val+bodyEnd.val ≤ Usize.max)
    (demand : FunctionStartDemand compiler ctx bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops compiler ctx typeIndex bodyBegin bodyEnd ⦃ out =>
        out.1 = .Ok () ∧ ∃ usedLocals usedControls,
          out.2.budget = {compiler.budget with locals := usedLocals,controls := usedControls} ∧
          usedLocals.val = compiler.budget.locals.val+ctx.locals.val.length ∧
          usedControls.val = compiler.budget.controls.val+1 ⦄ := by
  exact runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start.available
    ops bound available compiler ctx typeIndex signature bodyBegin bodyEnd lookup beginFits endFits demand

end Itasca.Compiler

end

end

/-! ## SlotAvailability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- The executable slot-range gate accepts an independent arithmetic bound. -/
theorem slot_availability_fit_accepts (function : runtime.bytecode.CompiledFunction) (start count : U32)
    (bounded : start.val + count.val ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.slots_fit function start count = .ok true := by
  have lower : start ≤ function.slot_count := by scalar_tac
  have accepts : runtime.bytecode.CompiledFunction.slots_fit function start count ⦃ result => result = true ⦄ := by
    unfold runtime.bytecode.CompiledFunction.slots_fit
    rw [if_pos lower]
    step as ⟨remaining,difference⟩
    have fits : count ≤ remaining := by scalar_tac
    simp [fits]
  obtain ⟨result,actual,rfl⟩ := WP.spec_imp_exists accepts
  exact actual

/-- Initializer instructions remain accepted in a larger final slot capacity,
as needed when composing active segment programs. -/
theorem initial_instruction_capacity_accepts (function : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (instruction : runtime.bytecode.Instr)
    (lowered : InitialInstruction function expr ty instruction)
    (capacity : (initializerWidth ty).val ≤ function.slot_count.val)
    (vector : ∀ lo hi, expr = .V128 lo hi → ty = .V128) :
    runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  have scalar : runtime.bytecode.CompiledFunction.slots_fit function 0#u32 1#u32 = .ok true := by
    apply slot_availability_fit_accepts
    have positive : 1 ≤ (initializerWidth ty).val := by cases ty <;> decide
    scalar_tac
  have wide (same : ty = .V128) :
      runtime.bytecode.CompiledFunction.slots_fit function 0#u32 2#u32 = .ok true := by
    apply slot_availability_fit_accepts
    simpa [same,initializerWidth] using capacity
  cases lowered <;>
    simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,runtime.bytecode.Instr.scalar,
      runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok]
  all_goals first | exact scalar | exact wide rfl | skip
  rename_i lo hi pool embedded
  rw [wide (vector lo hi rfl),bind_ok]
  have inside := (List.getElem?_eq_some_iff.mp embedded).1
  simpa [lift] using inside

end Itasca.Compiler

end

/-! ## BranchTableCapacity -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

theorem compiler_table_branch_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32) (lookup : before.table_depths.val[index.val]?=some depth)
    (accepted : runtime.compiler.control.FunctionCompiler.table_branch ops before index=.ok (.Ok (),after)) :
    capacityMetadata after=capacityMetadata before := by
  obtain ⟨target,budget,table,_,_,called⟩ := compiler_table_branch_success ops law before after index depth lookup accepted
  exact compiler_branch_capacity ops law {before with budget,function:={before.function with jump_tables:=table}}
    after depth 1#u32 false called

theorem TableBranchRun.capacity {A : Type} {ops : runtime.platform.Alloc A}
    (law : Platform.AllocCorrect ops) {before after : runtime.compiler.FunctionCompiler A}
    {index : Nat} (run : TableBranchRun ops before index after) :
    capacityMetadata after=capacityMetadata before := by
  induction run with
  | done => rfl
  | @cons before middle after index inside called rest ih =>
    exact ih.trans (compiler_table_branch_capacity ops law before middle index before.table_depths.val[index.val]
      (List.getElem?_eq_getElem inside) called)

theorem compiler_lower_table_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before=.ok (.Ok (),after)) :
    capacityMetadata after=capacityMetadata before := by
  obtain ⟨start,len,selector,emitted,_,_,_,emission,run⟩ := compiler_lower_table_success ops law before after accepted
  have retained := run.capacity law
  obtain ⟨budget,code,sources,rfl,_,_⟩ := emission
  exact retained

theorem compiler_br_table_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types=.ok (.Ok (),after)) :
    CapacityStep before after state := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table.inv ops before after state fallback types (.Ok ()) accepted with
  | @live labeled lowered cleared _ _ labelCall reachable lowerCall clearCall observed =>
    have frame := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.inv ops before labeled state fallback (.Ok ()) labelCall).frame
    have retained := compiler_lower_table_capacity ops law labeled lowered lowerCall
    have fields : lowered.function.local_slots = before.function.local_slots ∧
        lowered.function.slot_count = before.function.slot_count := by
      rw [frame] at retained
      simpa only [capacityMetadata, Prod.mk.injEq] using retained
    have post := compiler_observe_capacity_bound ops law {lowered with reachable := false, table_depths := cleared} after state (.Ok ()) observed
    exact ⟨post.1.trans fields.1, by simpa only [fields.1, fields.2] using post.2 rfl⟩
  | @dead labeled cleared _ _ labelCall dead clearCall observed =>
    have frame := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.inv ops before labeled state fallback (.Ok ()) labelCall).frame
    have post := compiler_observe_capacity_bound ops law {labeled with table_depths := cleared} after state (.Ok ()) observed
    rw [frame] at post
    exact ⟨post.1, post.2 rfl⟩

end Itasca.Compiler

end

/-! ## GlobalCapacity -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

theorem global_get_valid_bounds (compiled : runtime.bytecode.CompiledFunction)
    (ty : valtype) (dst index : U32)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid compiled
      (globalGetInstruction (decide (width ty = 2)) dst index) = .ok true) :
    dst.val + width ty ≤ compiled.slot_count.val := by
  by_cases vector : width ty = 2
  · simp only [vector,decide_true,globalGetInstruction,ite_true] at checked
    simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,runtime.bytecode.Instr.scalar,runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok] at checked
    have bound := slots_fit_true compiled dst 2#u32 checked
    rw [vector]
    scalar_tac
  · have widthEq : width ty = 1 := by cases ty <;> simp_all [width]
    simp only [widthEq,globalGetInstruction,show decide (1=2) = false from rfl,Bool.false_eq_true,ite_false] at checked
    simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,runtime.bytecode.Instr.scalar,runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok] at checked
    have bound := slots_fit_true compiled dst 1#u32 checked
    rw [widthEq]
    scalar_tac

end Itasca.Compiler

end

end
