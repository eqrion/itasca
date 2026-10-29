import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerMetadataTactic

/-!
Ordinary compiler effects of literal and basic scalar callbacks.

Main declarations: `compiler_op65_ordinary_result` and `compiler_drop_ordinary_result`. A direct consumer is `Compiler.Module.CompileSlice`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem compiler_op65_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 65#u16 a b bits = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  by_cases reach : before.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 65#u16 a b bits = (do
        let i ← lift (UScalar.cast .U32 bits)
        runtime.compiler.lower.FunctionCompiler.finish_op ops before
          state (runtime.bytecode.Instr.Const32 before.height i)) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reach]
      rfl
    rw [run] at accepted
    repeat' metadata_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    exact compiler_observe_ordinary_result ops law before after state status accepted

theorem compiler_op66_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 66#u16 a b bits = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  by_cases reach : before.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 66#u16 a b bits = (do
        let i ← lift (UScalar.cast .U64 bits)
        runtime.compiler.lower.FunctionCompiler.finish_op ops before
          state (runtime.bytecode.Instr.Const64 before.height i)) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reach]
      rfl
    rw [run] at accepted
    repeat' metadata_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    exact compiler_observe_ordinary_result ops law before after state status accepted

theorem compiler_op32_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 32#u16 a b bits = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  by_cases reach : before.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 32#u16 a b bits = (do
        let i ← lift (UScalar.cast .Usize a)
        let src ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U32)
            before.local_offsets i
        let i1 ← lift (UScalar.cast .Usize a)
        let vt ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
            _root_.Itasca.types.ValueType) before.function.locals i1
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
    repeat' metadata_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    exact compiler_observe_ordinary_result ops law before after state status accepted

theorem compiler_op33_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 33#u16 a b bits = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
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
              _root_.Itasca.types.ValueType) before.function.locals i1
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
    repeat' metadata_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    exact compiler_observe_ordinary_result ops law before after state status accepted

theorem compiler_op34_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 34#u16 a b bits = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
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
              _root_.Itasca.types.ValueType) before.function.locals i1
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
    repeat' metadata_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    exact compiler_observe_ordinary_result ops law before after state status accepted

theorem compiler_op16_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 16#u16 a b bits = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
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
    repeat' metadata_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    exact compiler_observe_ordinary_result ops law before after state status accepted

theorem compiler_op1_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 1#u16 a b bits = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  by_cases reach : before.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 1#u16 a b bits = (do
        runtime.compiler.FunctionCompiler.observe ops before state) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reach]
      rfl
    rw [run] at accepted
    repeat' metadata_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    exact compiler_observe_ordinary_result ops law before after state status accepted

theorem compiler_op26_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 26#u16 a b bits = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  by_cases reach : before.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state 26#u16 a b bits = (do
        runtime.compiler.FunctionCompiler.observe ops before state) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos reach]
      rfl
    rw [run] at accepted
    repeat' metadata_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    exact compiler_observe_ordinary_result ops law before after state status accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_i32_const_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : I32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const
      ops before state value = .ok (status, after)) : CompilerOrdinaryStable before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const at accepted
  simp only [lift, bind_ok] at accepted
  exact compiler_op65_ordinary_result ops law before after state _ _ _ status accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_i64_const_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : I64)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const
      ops before state value = .ok (status, after)) : CompilerOrdinaryStable before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const at accepted
  simp only [lift, bind_ok] at accepted
  exact compiler_op66_ordinary_result ops law before after state _ _ _ status accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_local_get_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_get
      ops before state value = .ok (status, after)) : CompilerOrdinaryStable before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_get at accepted
  exact compiler_op32_ordinary_result ops law before after state _ _ _ status accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_local_set_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_set
      ops before state value = .ok (status, after)) : CompilerOrdinaryStable before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_set at accepted
  exact compiler_op33_ordinary_result ops law before after state _ _ _ status accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_local_tee_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_tee
      ops before state value = .ok (status, after)) : CompilerOrdinaryStable before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_tee at accepted
  exact compiler_op34_ordinary_result ops law before after state _ _ _ status accepted

/-- Exact callback specialization of the checked ordinary field preservation. -/
theorem compiler_call_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (value : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_call
      ops before state value = .ok (status, after)) : CompilerOrdinaryStable before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_call at accepted
  exact compiler_op16_ordinary_result ops law before after state _ _ _ status accepted

theorem compiler_nop_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_nop
      ops before state = .ok (status, after)) : CompilerOrdinaryStable before after := by
  exact compiler_op1_ordinary_result ops law before after state _ _ _ status accepted

theorem compiler_drop_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (dropped : Itasca.code.StackType) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_drop
      ops before state dropped = .ok (status, after)) : CompilerOrdinaryStable before after := by
  exact compiler_op26_ordinary_result ops law before after state _ _ _ status accepted

end Itasca.Runtime.Code
