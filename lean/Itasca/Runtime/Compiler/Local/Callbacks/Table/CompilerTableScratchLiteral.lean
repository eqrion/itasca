import Itasca.Runtime.Compiler.Local.Lowering.Control.UnreachableContracts
import Itasca.Runtime.Compiler.Local.Relations.Table.StatefulAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Relations.Table.ControlTablePreservation
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables

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
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem compiler_branch_tables_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status, after)) :
    status = .Ok () → CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  intro success
  subst status
  exact compiler_branch_tables ops law before after depth skip conditional accepted

open Lean Meta Elab Tactic in
elab "control_tables_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  if lhs.getAppFn.constName? = some ``runtime.compiler.control.FunctionCompiler.branch then
    evalTactic (← `(tactic| have effect := compiler_branch_tables_result $ops $law _ _ _ _ _ _ $h))
  else
    evalTactic (← `(tactic| table_preservation_effect $h using $ops, $law))
macro "control_tables_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; table_preservation_close)
  | (fail_if_no_progress dsimp only at $h:ident)
  | solve | (control_tables_effect $h using $ops, $law; table_preservation_close)
  | solve | (sources_terminal $h; have output := (Prod.mk.inj (Result.ok.injEq.mp $h)).2; cases output; table_preservation_close)
  | (fail_if_no_progress simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | (sources_nonterminal $h
     obtain ⟨value, called, rest⟩ := bind_ok_inv _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue, secondValue⟩)
     | skip
     try control_tables_effect called using $ops, $law
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | sources_split $h)

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
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return at accepted
  repeat' control_tables_step accepted using ops, law

theorem compiler_br_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth types = .ok (.Ok (), after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br at accepted
  repeat' control_tables_step accepted using ops, law

theorem compiler_br_if_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth types = .ok (.Ok (), after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if at accepted
  repeat' control_tables_step accepted using ops, law


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
set_option maxHeartbeats 2000000
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
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end at accepted
  repeat' scratch_preservation_step accepted using ops, law
  all_goals try (casesm* core.result.Result Never _ <;> try casesm* Never)
  all_goals repeat' scratch_preservation_step accepted using ops, law

theorem compiler_else_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
      ops before state blockType = .ok (.Ok (), after)) :
    after.table_depths = before.table_depths := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else at accepted
  simp only [core.option.Option.take] at accepted
  repeat' scratch_preservation_step accepted using ops, law
  all_goals try (casesm* core.result.Result Never _ <;> try casesm* Never)
  all_goals repeat' scratch_preservation_step accepted using ops, law


end Itasca.Runtime.Compiler

end

/-! ## CompilerTableScratchCallbacks -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
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
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return at accepted
  repeat' scratch_preservation_step accepted using ops, law

theorem compiler_br_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth types = .ok (.Ok (), after)) :
    after.table_depths = before.table_depths := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br at accepted
  repeat' scratch_preservation_step accepted using ops, law

theorem compiler_br_if_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth types = .ok (.Ok (), after)) :
    after.table_depths = before.table_depths := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if at accepted
  repeat' scratch_preservation_step accepted using ops, law


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
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
theorem compiler_op65_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 65#u16 a b bits = .ok (.Ok (), after)) :
    after.table_depths = before.table_depths := by
  by_cases reach : before.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 65#u16 a b bits = (do
        let i ← lift (UScalar.cast .U32 bits)
        runtime.compiler.lower.FunctionCompiler.finish_op ops before
          state (runtime.bytecode.Instr.Const32 before.height i)) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reach]
      rfl
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
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 66#u16 a b bits = (do
        let i ← lift (UScalar.cast .U64 bits)
        runtime.compiler.lower.FunctionCompiler.finish_op ops before
          state (runtime.bytecode.Instr.Const64 before.height i)) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reach]
      rfl
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
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 32#u16 a b bits = (do
        let i ← lift (UScalar.cast .Usize a)
        let src ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U32)
            before.local_offsets i
        let i1 ← lift (UScalar.cast .Usize a)
        let vt ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
            _root_.Itasca.wasm_types.ValueType) before.function.locals i1
        let n ← runtime.value.width vt
        let (r, self1) ←
          runtime.compiler.FunctionCompiler.copy ops before
            before.height src n
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          runtime.compiler.FunctionCompiler.observe ops self1 state
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r1 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
              residual
          Result.ok (r1, self1)) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reach]
      rfl
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
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 33#u16 a b bits = (do
        let i ← lift (UScalar.cast .Usize a)
        let dst ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U32)
            before.local_offsets i
        let r ←
          runtime.compiler.FunctionCompiler.operand ops before
            1#usize
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val =>
          let i1 ← lift (UScalar.cast .Usize a)
          let vt ←
            alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
              _root_.Itasca.wasm_types.ValueType) before.function.locals i1
          let n ← runtime.value.width vt
          let (r1, self1) ←
            runtime.compiler.FunctionCompiler.copy ops before dst val
              n
          let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
          match cf1 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            runtime.compiler.FunctionCompiler.observe ops self1 state
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r2 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
                residual
            Result.ok (r2, self1)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r1 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
              residual
          Result.ok (r1, before)) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reach]
      rfl
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
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 34#u16 a b bits = (do
        let i ← lift (UScalar.cast .Usize a)
        let dst ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U32)
            before.local_offsets i
        let r ←
          runtime.compiler.FunctionCompiler.operand ops before
            1#usize
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val =>
          let i1 ← lift (UScalar.cast .Usize a)
          let vt ←
            alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
              _root_.Itasca.wasm_types.ValueType) before.function.locals i1
          let n ← runtime.value.width vt
          let (r1, self1) ←
            runtime.compiler.FunctionCompiler.copy ops before dst val
              n
          let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
          match cf1 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            runtime.compiler.FunctionCompiler.observe ops self1 state
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r2 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
                residual
            Result.ok (r2, self1)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r1 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
              residual
          Result.ok (r1, before)) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reach]
      rfl
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
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 16#u16 a b bits = (do
        let i ← lift (UScalar.cast .Usize a)
        let slots ← Slice.index_usize before.func_param_slots i
        let o ← lift (U32.checked_sub before.height slots)
        let r ←
          core.option.Option.ok_or o _root_.Itasca.error.VisitError.OutOfMemory
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val =>
          runtime.compiler.lower.FunctionCompiler.finish_op ops
            before state (runtime.bytecode.Instr.Call a val)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r1 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
              residual
          Result.ok (r1, before)) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reach]
      rfl
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
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 1#u16 a b bits = (do
        runtime.compiler.FunctionCompiler.observe ops before state) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reach]
      rfl
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
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 26#u16 a b bits = (do
        runtime.compiler.FunctionCompiler.observe ops before state) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reach]
      rfl
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
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const at accepted
  simp only [lift, bind_ok] at accepted
  exact compiler_op65_depths ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_i64_const_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : I64)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const
      ops before state value = .ok (.Ok (), after)) : after.table_depths = before.table_depths := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const at accepted
  simp only [lift, bind_ok] at accepted
  exact compiler_op66_depths ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_local_get_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_get
      ops before state value = .ok (.Ok (), after)) : after.table_depths = before.table_depths := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_get at accepted
  exact compiler_op32_depths ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_local_set_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_set
      ops before state value = .ok (.Ok (), after)) : after.table_depths = before.table_depths := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_set at accepted
  exact compiler_op33_depths ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_local_tee_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_tee
      ops before state value = .ok (.Ok (), after)) : after.table_depths = before.table_depths := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_tee at accepted
  exact compiler_op34_depths ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_call_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_call
      ops before state value = .ok (.Ok (), after)) : after.table_depths = before.table_depths := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_call at accepted
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
