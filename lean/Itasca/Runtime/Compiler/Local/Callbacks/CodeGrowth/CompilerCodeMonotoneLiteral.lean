import Itasca.Runtime.Compiler.Local.Lowering.Emission.Emit
import Itasca.Runtime.Compiler.Local.Capacity.EmissionGrowth
import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth.PatchGrowth
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericOperands
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatEncoding
import Itasca.Runtime.Compiler.Local.Relations.Emission.CoreLoweringEffects
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulSuccess
import Itasca.Runtime.Compiler.Local.Relations.Calls.StatefulCallbacks

/-!
Sections, each formerly its own module: CompilerCodeMonotone, CompilerCodeMonotoneTactic, CompilerCodeMonotoneScalar, CompilerCodeMonotoneStateful, CompilerCodeMonotoneLiteral.
-/

/-! ## CompilerCodeMonotone -/

section

/-!
Emitted-code monotonicity of compiler primitives.

Main declarations: `compiler_emit_code_mono` and `compiler_fixups_after_if_code_mono`. A direct consumer is `Compiler.Local.Callbacks.CodeGrowth.CompilerCodeMonotoneTactic`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
theorem compiler_emit_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status, after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  have code := ((runtime.compiler.FunctionCompiler.emit.inv ops before after instruction status accepted).2 law).1
  rcases code with unchanged | appended
  · rw [unchanged]
  · rw [appended, List.length_append, List.length_singleton]
    omega

theorem compiler_copy_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (dst src count : U32) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (status, after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  unfold runtime.compiler.FunctionCompiler.copy at accepted
  split at accepted
  · have same : before = after := (Prod.mk.inj (Result.ok.injEq.mp accepted)).2
    subst after
    omega
  · split at accepted
    · have same : before = after := (Prod.mk.inj (Result.ok.injEq.mp accepted)).2
      subst after
      omega
    · obtain ⟨instruction, _, emitted⟩ := bind_ok_inv _ _ _ accepted
      exact compiler_emit_code_mono ops law before after instruction status emitted

theorem compiler_finish_op_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (instruction : runtime.bytecode.Instr)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.finish_op ops before state instruction = .ok (status, after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  unfold runtime.compiler.lower.FunctionCompiler.finish_op at accepted
  obtain ⟨⟨result, middle⟩, emitted, rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨_, output⟩ := rest
      subst after
      exact compiler_emit_code_mono ops law before middle instruction (.Err error) emitted
  | Ok value =>
    cases value
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    rw [compiler_observe_code_result ops law middle after state status rest]
    exact compiler_emit_code_mono ops law before middle instruction (.Ok ()) emitted

theorem compiler_observe_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.observe ops before state = .ok (status, after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  rw [compiler_observe_code_result ops law before after state status accepted]

theorem compiler_pair_code_mono {A : Type} (ops : runtime.platform.Alloc A)
     (before after : runtime.compiler.FunctionCompiler A) (a b : U32)
    (status : core.result.Result U32 Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.pair ops before a b = .ok (status, after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  rw [compiler_pair_code_result ops before after a b status accepted]

theorem compiler_pc_code_mono {A : Type} (ops : runtime.platform.Alloc A)
     (before after : runtime.compiler.FunctionCompiler A)
    (status : core.result.Result U32 Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.pc ops before = .ok (status, after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  rw [compiler_pc_code_result ops before after status accepted]

theorem compiler_patch_code_mono {A : Type} (ops : runtime.platform.Alloc A)
     (before after : runtime.compiler.FunctionCompiler A) (pc : Usize) (target : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.patch ops before pc target = .ok (status, after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  rw [compiler_patch_code_length ops before after pc target status accepted]

theorem compiler_fixups_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0
      ops before sites target index status = .ok output) :
    before.function.code.val.length ≤ (snapshotCompiler output).function.code.val.length := by
  rw [compiler_fixups_code_length ops before sites target index status output accepted]

theorem compiler_fixups_after_if_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop1
      ops before sites target index status = .ok output) :
    before.function.code.val.length ≤ (snapshotCompiler output).function.code.val.length := by
  rw [compiler_fixups_after_if_code_length ops before sites target index status output accepted]

end Itasca.Runtime.Compiler

end

/-! ## CompilerCodeMonotoneTactic -/

section

/-!
Proof automation for compiler code-monotonicity obligations.

Main declarations: `code_mono_effect` and `code_mono_close`. A direct consumer is `Compiler.Local.Callbacks.CodeGrowth.CompilerCodeMonotoneLiteral`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open Lean Meta Elab Tactic in
elab "code_mono_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  let some functionName := lhs.getAppFn.constName? | throwError "not a named helper"
  let tac ← match functionName with
    | ``runtime.compiler.FunctionCompiler.pair =>
      `(tactic| have effect := compiler_pair_code_mono $ops _ _ _ _ _ $h)
    | ``runtime.compiler.control.FunctionCompiler.branch => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_branch_code_mono
      `(tactic| have effect := $theoremName $ops $law _ _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.observe =>
      `(tactic| have effect := compiler_observe_code_mono $ops $law _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.emit =>
      `(tactic| have effect := compiler_emit_code_mono $ops $law _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.copy =>
      `(tactic| have effect := compiler_copy_code_mono $ops $law _ _ _ _ _ _ $h)
    | ``runtime.compiler.lower.FunctionCompiler.finish_op =>
      `(tactic| have effect := compiler_finish_op_code_mono $ops $law _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.pc => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_pc_code_mono
      `(tactic| have effect := $theoremName $ops _ _ _ $h)
    | ``runtime.compiler.control.FunctionCompiler.patch => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_patch_code_mono
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0 => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_fixups_code_mono
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop1 => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_fixups_after_if_code_mono
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ _ $h)
    | _ => throwError "not a compiler helper"
  evalTactic tac


macro "code_mono_close" : tactic => `(tactic|
  (first | rfl | (simp_all [snapshotCompiler, source_unit_eq]; try omega)))
macro "code_mono_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; code_mono_close)
  | (fail_if_no_progress dsimp only at $h:ident)
  | solve | (code_mono_effect $h using $ops, $law; code_mono_close)
  | solve | (sources_terminal $h; have output := (Prod.mk.inj (Result.ok.injEq.mp $h)).2; cases output; code_mono_close)
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
     try code_mono_effect called using $ops, $law
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | sources_split $h)



end Itasca.Runtime.Compiler

end

/-! ## CompilerCodeMonotoneScalar -/

section

/-!
Emitted-code monotonicity of numeric and core scalar callbacks.

Main declarations: `compiler_numeric_code_mono` and `compiler_core_code_mono`. A direct consumer is `Compiler.Local.Coordinates.LoweringTargetBounds`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem compiler_numeric_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : SourceMachine.Numeric.Instruction)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (integerOpcode op) 0#u32 0#u32 0#u128 = .ok (.Ok (), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  by_cases reach : before.reachable = true
  · rw [lower_numeric_dispatch ops before state op reach] at accepted
    unfold numericLowering at accepted
    repeat' code_mono_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_code_mono ops law before after state (.Ok ()) accepted

theorem compiler_float_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : SourceMachine.Float.Instruction)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (floatOpcode op) 0#u32 0#u32 0#u128 = .ok (.Ok (), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  by_cases reach : before.reachable = true
  · rw [lower_float_dispatch ops before state op reach] at accepted
    unfold floatLowering at accepted
    repeat' code_mono_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_code_mono ops law before after state (.Ok ()) accepted

theorem compiler_core_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : CoreOperation)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state op.opcode op.first op.second 0#u128 = .ok ((.Ok ()), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  by_cases reach : before.reachable = true
  · rw [lower_core_dispatch ops before state op reach] at accepted
    cases op <;> unfold coreLowering at accepted
    all_goals simp only [selectLowering, globalGetLowering, globalSetLowering,
      memoryLoadLowering, memoryStoreLowering] at accepted
    all_goals repeat' code_mono_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_code_mono ops law before after state (.Ok ()) accepted

end Itasca.Runtime.Compiler

end

/-! ## CompilerCodeMonotoneStateful -/

section

/-!
Emitted-code monotonicity of stateful and indirect-call callbacks.

Main declarations: `compiler_stateful_code_mono` and `compiler_indirect_call_code_mono`. A direct consumer is `Compiler.Local.Publication.LiteralMapPublication`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem compiler_stateful_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : SourceMachine.Stateful.Instruction) (a b : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (statefulOpcode op) a b 0#u128 = .ok (status, after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  by_cases reach : before.reachable = true
  · rw [lower_stateful_dispatch ops before state op a b reach] at accepted
    cases op <;> simp only [statefulLowering] at accepted
    all_goals repeat' code_mono_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_code_mono ops law before after state status accepted
theorem compiler_indirect_call_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 17#u16 a b 0#u128 = .ok (status, after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  by_cases reach : before.reachable = true
  · rw [lower_indirect_call_dispatch ops before state a b reach] at accepted
    unfold indirectCallLowering at accepted
    repeat' code_mono_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_code_mono ops law before after state status accepted
end Itasca.Runtime.Compiler

end

/-! ## CompilerCodeMonotoneLiteral -/

section

/-!
Emitted-code monotonicity of literal and basic scalar callbacks.

Main declarations: `compiler_op65_code_mono` and `compiler_drop_code_mono`. A direct consumer is `Compiler.Local.Publication.LiteralMapPublication`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
theorem compiler_op65_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 65#u16 a b bits = .ok (.Ok (), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  by_cases reach : before.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 65#u16 a b bits = (do
        let i ← lift (UScalar.cast .U32 bits)
        runtime.compiler.lower.FunctionCompiler.finish_op ops before
          state (runtime.bytecode.Instr.Const32 before.height i)) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reach]
      rfl
    rw [run] at accepted
    repeat' code_mono_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_code_mono ops law before after state (.Ok ()) accepted

theorem compiler_op66_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 66#u16 a b bits = .ok (.Ok (), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  by_cases reach : before.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 66#u16 a b bits = (do
        let i ← lift (UScalar.cast .U64 bits)
        runtime.compiler.lower.FunctionCompiler.finish_op ops before
          state (runtime.bytecode.Instr.Const64 before.height i)) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reach]
      rfl
    rw [run] at accepted
    repeat' code_mono_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_code_mono ops law before after state (.Ok ()) accepted

theorem compiler_op32_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 32#u16 a b bits = .ok (.Ok (), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
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
    repeat' code_mono_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_code_mono ops law before after state (.Ok ()) accepted

theorem compiler_op33_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 33#u16 a b bits = .ok (.Ok (), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
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
    repeat' code_mono_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_code_mono ops law before after state (.Ok ()) accepted

theorem compiler_op34_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 34#u16 a b bits = .ok (.Ok (), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
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
    repeat' code_mono_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_code_mono ops law before after state (.Ok ()) accepted

theorem compiler_op16_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 16#u16 a b bits = .ok (.Ok (), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
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
    repeat' code_mono_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_code_mono ops law before after state (.Ok ()) accepted

theorem compiler_op1_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 1#u16 a b bits = .ok (.Ok (), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  by_cases reach : before.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 1#u16 a b bits = (do
        runtime.compiler.FunctionCompiler.observe ops before state) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reach]
      rfl
    rw [run] at accepted
    repeat' code_mono_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_code_mono ops law before after state (.Ok ()) accepted

theorem compiler_op26_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 26#u16 a b bits = .ok (.Ok (), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  by_cases reach : before.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 26#u16 a b bits = (do
        runtime.compiler.FunctionCompiler.observe ops before state) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reach]
      rfl
    rw [run] at accepted
    repeat' code_mono_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_code_mono ops law before after state (.Ok ()) accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_i32_const_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : I32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const
      ops before state value = .ok (.Ok (), after)) : before.function.code.val.length ≤ after.function.code.val.length := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const at accepted
  simp only [lift, bind_ok] at accepted
  exact compiler_op65_code_mono ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_i64_const_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : I64)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const
      ops before state value = .ok (.Ok (), after)) : before.function.code.val.length ≤ after.function.code.val.length := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const at accepted
  simp only [lift, bind_ok] at accepted
  exact compiler_op66_code_mono ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_local_get_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_get
      ops before state value = .ok (.Ok (), after)) : before.function.code.val.length ≤ after.function.code.val.length := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_get at accepted
  exact compiler_op32_code_mono ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_local_set_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_set
      ops before state value = .ok (.Ok (), after)) : before.function.code.val.length ≤ after.function.code.val.length := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_set at accepted
  exact compiler_op33_code_mono ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_local_tee_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_tee
      ops before state value = .ok (.Ok (), after)) : before.function.code.val.length ≤ after.function.code.val.length := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_tee at accepted
  exact compiler_op34_code_mono ops law before after state _ _ _ accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_call_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_call
      ops before state value = .ok (.Ok (), after)) : before.function.code.val.length ≤ after.function.code.val.length := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_call at accepted
  exact compiler_op16_code_mono ops law before after state _ _ _ accepted

theorem compiler_nop_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_nop
      ops before state = .ok (.Ok (), after)) : before.function.code.val.length ≤ after.function.code.val.length := by
  exact compiler_op1_code_mono ops law before after state _ _ _ accepted

theorem compiler_drop_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (dropped : Itasca.code.StackType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_drop
      ops before state dropped = .ok (.Ok (), after)) : before.function.code.val.length ≤ after.function.code.val.length := by
  exact compiler_op26_code_mono ops law before after state _ _ _ accepted


end Itasca.Runtime.Compiler

end
