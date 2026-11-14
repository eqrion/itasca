import Itasca.Runtime.Compiler.Local.Callbacks.CallbackEquations
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericOperands
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatEncoding
import Itasca.Runtime.Compiler.Local.Relations.Emission.CoreLoweringEffects

/-!
Sections, each formerly its own module: LiteralTablePreservation, ScalarTablePreservation.
-/

/-! ## LiteralTablePreservation -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
theorem compiler_op65_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 65#u16 a b bits = .ok (.Ok (), after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  by_cases reach : before.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.i32_const ops before state a b bits reach
    rw [run] at accepted
    repeat' table_preservation_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_tables ops law before after state (.Ok ()) accepted

theorem compiler_op66_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 66#u16 a b bits = .ok (.Ok (), after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  by_cases reach : before.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.i64_const ops before state a b bits reach
    rw [run] at accepted
    repeat' table_preservation_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_tables ops law before after state (.Ok ()) accepted

theorem compiler_op32_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 32#u16 a b bits = .ok (.Ok (), after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  by_cases reach : before.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.local_get ops before state a b bits reach
    rw [run] at accepted
    repeat' table_preservation_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_tables ops law before after state (.Ok ()) accepted

theorem compiler_op33_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 33#u16 a b bits = .ok (.Ok (), after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  by_cases reach : before.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.local_set ops before state a b bits reach
    rw [run] at accepted
    repeat' table_preservation_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_tables ops law before after state (.Ok ()) accepted

theorem compiler_op34_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 34#u16 a b bits = .ok (.Ok (), after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  by_cases reach : before.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.local_tee ops before state a b bits reach
    rw [run] at accepted
    repeat' table_preservation_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_tables ops law before after state (.Ok ()) accepted

theorem compiler_op16_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 16#u16 a b bits = .ok (.Ok (), after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  by_cases reach : before.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.call ops before state a b bits reach
    rw [run] at accepted
    repeat' table_preservation_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_tables ops law before after state (.Ok ()) accepted

theorem compiler_op1_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 1#u16 a b bits = .ok (.Ok (), after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  by_cases reach : before.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.nop ops before state a b bits reach
    rw [run] at accepted
    repeat' table_preservation_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_tables ops law before after state (.Ok ()) accepted

theorem compiler_op26_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 26#u16 a b bits = .ok (.Ok (), after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  by_cases reach : before.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.drop ops before state a b bits reach
    rw [run] at accepted
    repeat' table_preservation_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_tables ops law before after state (.Ok ()) accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_i32_const_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : I32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const
      ops before state value = .ok (.Ok (), after)) : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const.eq] at accepted
  simp only [lift, bind_ok] at accepted
  exact compiler_op65_tables ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_i64_const_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : I64)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const
      ops before state value = .ok (.Ok (), after)) : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const.eq] at accepted
  simp only [lift, bind_ok] at accepted
  exact compiler_op66_tables ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_local_get_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_get
      ops before state value = .ok (.Ok (), after)) : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_get.eq] at accepted
  exact compiler_op32_tables ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_local_set_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_set
      ops before state value = .ok (.Ok (), after)) : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_set.eq] at accepted
  exact compiler_op33_tables ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_local_tee_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_tee
      ops before state value = .ok (.Ok (), after)) : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_tee.eq] at accepted
  exact compiler_op34_tables ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_call_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_call
      ops before state value = .ok (.Ok (), after)) : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_call.eq] at accepted
  exact compiler_op16_tables ops law before after state _ _ _ accepted

theorem compiler_nop_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_nop
      ops before state = .ok (.Ok (), after)) : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  exact compiler_op1_tables ops law before after state _ _ _ accepted

theorem compiler_drop_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (dropped : Itasca.code.StackType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_drop
      ops before state dropped = .ok (.Ok (), after)) : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  exact compiler_op26_tables ops law before after state _ _ _ accepted


end Itasca.Runtime.Compiler

end

/-! ## ScalarTablePreservation -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
theorem compiler_numeric_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : SourceMachine.Numeric.Instruction)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (integerOpcode op) 0#u32 0#u32 0#u128 = .ok (.Ok (), after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  by_cases reach : before.reachable = true
  · rw [lower_numeric_dispatch ops before state op reach] at accepted
    unfold numericLowering at accepted
    repeat' table_preservation_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_tables ops law before after state (.Ok ()) accepted

theorem compiler_float_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : SourceMachine.Float.Instruction)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (floatOpcode op) 0#u32 0#u32 0#u128 = .ok (.Ok (), after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  by_cases reach : before.reachable = true
  · rw [lower_float_dispatch ops before state op reach] at accepted
    unfold floatLowering at accepted
    repeat' table_preservation_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_tables ops law before after state (.Ok ()) accepted

theorem compiler_core_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : CoreOperation)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state op.opcode op.first op.second 0#u128 = .ok ((.Ok ()), after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  by_cases reach : before.reachable = true
  · rw [lower_core_dispatch ops before state op reach] at accepted
    cases op <;> unfold coreLowering at accepted
    all_goals simp only [selectLowering, globalGetLowering, globalSetLowering,
      memoryLoadLowering, memoryStoreLowering] at accepted
    all_goals repeat' table_preservation_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_tables ops law before after state (.Ok ()) accepted

end Itasca.Runtime.Compiler

end
