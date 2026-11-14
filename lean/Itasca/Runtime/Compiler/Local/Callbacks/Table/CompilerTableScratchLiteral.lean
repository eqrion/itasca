import Itasca.Runtime.Compiler.Local.Callbacks.CallbackEquations
import Itasca.Runtime.Compiler.Local.Callbacks.Control.BranchCallbacks
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EndContracts
import Itasca.Runtime.Compiler.Local.Lowering.Control.ReturnContracts
import Itasca.Runtime.Compiler.Local.Lowering.Control.UnreachableContracts
import Itasca.Runtime.Compiler.Local.Relations.Table.StatefulAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Relations.Table.ControlTablePreservation
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseContracts

/-!
Sections, each formerly its own module: CompilerPairTableAppend, CallbackTables, CompilerTableScratchControl, CompilerTableScratchCallbacks, CompilerTableScratchLiteral.
-/

/-! ## CompilerPairTableAppend -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std

theorem compiler_tables_pair_append (before after : runtime.bytecode.CompiledFunction)
    (extra : List (U32 × U32))
    (pairs : after.indirect.val = before.indirect.val ++ extra)
    (auxiliary : compilerAuxiliaryTables after = compilerAuxiliaryTables before) :
    CompilerTables.ofFunction after = (CompilerTables.ofFunction before).append ⟨extra,[],[],[]⟩ := by
  simp only [compilerAuxiliaryTables, Prod.mk.injEq] at auxiliary
  obtain ⟨simd,constants,jumps⟩ := auxiliary
  simp only [CompilerTables.ofFunction,CompilerTables.append,CompilerTables.mk.injEq,List.append_nil]
  exact ⟨pairs,simd,constants,jumps⟩
end Itasca.Runtime.Compiler

end

/-! ## CallbackTables -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096


theorem compiler_unreachable_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
      ops before state = .ok (.Ok (), after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  have frame := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable.inv ops before after state (.Ok ()) accepted).frame
  rw [frame]
  rfl

theorem compiler_return_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
      ops before state = .ok (.Ok (), after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  have frame := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return.inv ops before after state (.Ok ()) accepted).frame
  rw [frame]
  rfl

theorem compiler_br_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth types = .ok (.Ok (), after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  clear law
  rw [(runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br.inv ops before after state depth types (.Ok ()) accepted).frame]
  rfl

theorem compiler_br_if_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth types = .ok (.Ok (), after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  clear law
  rw [(runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if.inv ops before after state depth types (.Ok ()) accepted).frame]
  rfl

theorem compiler_block_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_block
      ops before state bt = .ok (.Ok (), after)) : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  exact compiler_enter_tables ops law before after state .Block bt accepted

theorem compiler_loop_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_loop
      ops before state bt = .ok (.Ok (), after)) : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  exact compiler_enter_tables ops law before after state .Loop bt accepted

theorem compiler_if_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_if
      ops before state bt = .ok (.Ok (), after)) : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  exact compiler_enter_tables ops law before after state .Then bt accepted

end Itasca.Runtime.Compiler

end

/-! ## CompilerTableScratchControl -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
theorem compiler_enter_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind)
    (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.control.FunctionCompiler.enter ops before state kind blockType = .ok (.Ok (), after)) :
    after.table_depths = before.table_depths := by
  clear law
  have frame := (runtime.compiler.control.FunctionCompiler.enter.inv ops before after state kind blockType (.Ok ()) accepted).1
  change after = _ at frame
  rw [frame]


theorem compiler_end_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind)
    (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
      ops before state kind blockType = .ok (.Ok (), after)) :
    after.table_depths = before.table_depths := by
  have frame := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end.inv ops before after state kind blockType (.Ok ()) accepted).frame
  rw [frame]

theorem compiler_else_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
      ops before state blockType = .ok (.Ok (), after)) :
    after.table_depths = before.table_depths := by
  have effect := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.inv
    ops before after state blockType (.Ok ()) accepted
  have frame := effect.frame
  change after = _ at frame
  rw [frame]


end Itasca.Runtime.Compiler

end

/-! ## CompilerTableScratchCallbacks -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
theorem compiler_unreachable_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
      ops before state = .ok (.Ok (), after)) :
    after.table_depths = before.table_depths := by
  have frame := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable.inv ops before after state (.Ok ()) accepted).frame
  rw [frame]

theorem compiler_return_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
      ops before state = .ok (.Ok (), after)) :
    after.table_depths = before.table_depths := by
  have frame := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return.inv ops before after state (.Ok ()) accepted).frame
  rw [frame]

theorem compiler_br_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth types = .ok (.Ok (), after)) :
    after.table_depths = before.table_depths := by
  clear law
  rw [(runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br.inv ops before after state depth types (.Ok ()) accepted).frame]

theorem compiler_br_if_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth types = .ok (.Ok (), after)) :
    after.table_depths = before.table_depths := by
  clear law
  rw [(runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if.inv ops before after state depth types (.Ok ()) accepted).frame]

theorem compiler_block_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_block
      ops before state bt = .ok (.Ok (), after)) : after.table_depths = before.table_depths := by
  exact compiler_enter_depths ops law before after state .Block bt accepted

theorem compiler_loop_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_loop
      ops before state bt = .ok (.Ok (), after)) : after.table_depths = before.table_depths := by
  exact compiler_enter_depths ops law before after state .Loop bt accepted

theorem compiler_if_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_if
      ops before state bt = .ok (.Ok (), after)) : after.table_depths = before.table_depths := by
  exact compiler_enter_depths ops law before after state .Then bt accepted

end Itasca.Runtime.Compiler

end

/-! ## CompilerTableScratchLiteral -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
theorem compiler_op65_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 65#u16 a b bits = .ok (.Ok (), after)) :
    after.table_depths = before.table_depths := by
  by_cases reach : before.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.i32_const ops before state a b bits reach
    rw [run] at accepted
    repeat' scratch_preservation_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_depths ops law before after state (.Ok ()) accepted

theorem compiler_op66_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 66#u16 a b bits = .ok (.Ok (), after)) :
    after.table_depths = before.table_depths := by
  by_cases reach : before.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.i64_const ops before state a b bits reach
    rw [run] at accepted
    repeat' scratch_preservation_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_depths ops law before after state (.Ok ()) accepted

theorem compiler_op32_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 32#u16 a b bits = .ok (.Ok (), after)) :
    after.table_depths = before.table_depths := by
  by_cases reach : before.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.local_get ops before state a b bits reach
    rw [run] at accepted
    repeat' scratch_preservation_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_depths ops law before after state (.Ok ()) accepted

theorem compiler_op33_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 33#u16 a b bits = .ok (.Ok (), after)) :
    after.table_depths = before.table_depths := by
  by_cases reach : before.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.local_set ops before state a b bits reach
    rw [run] at accepted
    repeat' scratch_preservation_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_depths ops law before after state (.Ok ()) accepted

theorem compiler_op34_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 34#u16 a b bits = .ok (.Ok (), after)) :
    after.table_depths = before.table_depths := by
  by_cases reach : before.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.local_tee ops before state a b bits reach
    rw [run] at accepted
    repeat' scratch_preservation_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_depths ops law before after state (.Ok ()) accepted

theorem compiler_op16_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 16#u16 a b bits = .ok (.Ok (), after)) :
    after.table_depths = before.table_depths := by
  by_cases reach : before.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.call ops before state a b bits reach
    rw [run] at accepted
    repeat' scratch_preservation_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_depths ops law before after state (.Ok ()) accepted

theorem compiler_op1_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 1#u16 a b bits = .ok (.Ok (), after)) :
    after.table_depths = before.table_depths := by
  by_cases reach : before.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.nop ops before state a b bits reach
    rw [run] at accepted
    repeat' scratch_preservation_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_depths ops law before after state (.Ok ()) accepted

theorem compiler_op26_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 26#u16 a b bits = .ok (.Ok (), after)) :
    after.table_depths = before.table_depths := by
  by_cases reach : before.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.drop ops before state a b bits reach
    rw [run] at accepted
    repeat' scratch_preservation_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_depths ops law before after state (.Ok ()) accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_i32_const_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : I32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const
      ops before state value = .ok (.Ok (), after)) : after.table_depths = before.table_depths := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const.eq] at accepted
  simp only [lift, bind_ok] at accepted
  exact compiler_op65_depths ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_i64_const_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : I64)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const
      ops before state value = .ok (.Ok (), after)) : after.table_depths = before.table_depths := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const.eq] at accepted
  simp only [lift, bind_ok] at accepted
  exact compiler_op66_depths ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_local_get_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_get
      ops before state value = .ok (.Ok (), after)) : after.table_depths = before.table_depths := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_get.eq] at accepted
  exact compiler_op32_depths ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_local_set_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_set
      ops before state value = .ok (.Ok (), after)) : after.table_depths = before.table_depths := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_set.eq] at accepted
  exact compiler_op33_depths ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_local_tee_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_tee
      ops before state value = .ok (.Ok (), after)) : after.table_depths = before.table_depths := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_tee.eq] at accepted
  exact compiler_op34_depths ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_call_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_call
      ops before state value = .ok (.Ok (), after)) : after.table_depths = before.table_depths := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_call.eq] at accepted
  exact compiler_op16_depths ops law before after state _ _ _ accepted

theorem compiler_nop_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_nop
      ops before state = .ok (.Ok (), after)) : after.table_depths = before.table_depths := by
  exact compiler_op1_depths ops law before after state _ _ _ accepted

theorem compiler_drop_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (dropped : Itasca.code.StackType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_drop
      ops before state dropped = .ok (.Ok (), after)) : after.table_depths = before.table_depths := by
  exact compiler_op26_depths ops law before after state _ _ _ accepted


end Itasca.Runtime.Compiler

end
