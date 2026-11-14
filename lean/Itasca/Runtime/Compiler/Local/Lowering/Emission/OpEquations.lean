import Mathlib.Tactic.IntervalCases
import Itasca.Generated.FunsCompiler

/-!
Low-level equations for the compiler opcode dispatcher. This leaf imports only
its generated implementation so callback proofs can share exact live-branch
reductions without importing emission or copy contracts.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- A dead compiler state bypasses opcode dispatch and only observes input. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.dead {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (dead : before.reachable = false) :
    runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits =
      runtime.compiler.FunctionCompiler.observe ops before state := by
  unfold runtime.compiler.lower.FunctionCompiler.op
  exact if_neg (by simp only [dead, Bool.false_eq_true, not_false_eq_true])

/-- The live nop opcode observes the current validator state. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.nop {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 1#u16 a b bits =
      runtime.compiler.FunctionCompiler.observe ops before state := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- The live drop opcode observes the current validator state. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.drop {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 26#u16 a b bits =
      runtime.compiler.FunctionCompiler.observe ops before state := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- The live direct-call opcode checks parameter slots before emitting a call. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.call {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 16#u16 a b bits = (do
      let i ← lift (UScalar.cast .Usize a)
      let slots ← Slice.index_usize before.func_param_slots i
      let o ← lift (U32.checked_sub before.height slots)
      let r ← core.option.Option.ok_or o Itasca.error.VisitError.OutOfMemory
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | .Continue val => runtime.compiler.lower.FunctionCompiler.finish_op ops before state (.Call a val)
      | .Break residual => do
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
          (core.convert.FromSame Itasca.error.VisitError) residual
        Result.ok (r1, before)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- The live local.get opcode copies the indexed local into the operand stack. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.local_get {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 32#u16 a b bits = (do
      let i ← lift (UScalar.cast .Usize a)
      let src ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) before.local_offsets i
      let i1 ← lift (UScalar.cast .Usize a)
      let vt ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Itasca.wasm_types.ValueType)
        before.function.locals i1
      let n ← runtime.value.width vt
      let (r, after) ← runtime.compiler.FunctionCompiler.copy ops before before.height src n
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | .Continue _ => runtime.compiler.FunctionCompiler.observe ops after state
      | .Break residual => do
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
          (core.convert.FromSame Itasca.error.VisitError) residual
        Result.ok (r1, after)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- The live local.set opcode reads the top value and copies it to its local. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.local_set {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 33#u16 a b bits = (do
      let i ← lift (UScalar.cast .Usize a)
      let dst ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) before.local_offsets i
      let r ← runtime.compiler.FunctionCompiler.operand ops before 1#usize
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | .Continue val => do
        let i1 ← lift (UScalar.cast .Usize a)
        let vt ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Itasca.wasm_types.ValueType)
          before.function.locals i1
        let n ← runtime.value.width vt
        let (r1, after) ← runtime.compiler.FunctionCompiler.copy ops before dst val n
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | .Continue _ => runtime.compiler.FunctionCompiler.observe ops after state
        | .Break residual => do
          let r2 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
            (core.convert.FromSame Itasca.error.VisitError) residual
          Result.ok (r2, after)
      | .Break residual => do
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
          (core.convert.FromSame Itasca.error.VisitError) residual
        Result.ok (r1, before)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- The live local.tee opcode copies the top value to its local and observes it. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.local_tee {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 34#u16 a b bits = (do
      let i ← lift (UScalar.cast .Usize a)
      let dst ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) before.local_offsets i
      let r ← runtime.compiler.FunctionCompiler.operand ops before 1#usize
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | .Continue val => do
        let i1 ← lift (UScalar.cast .Usize a)
        let vt ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Itasca.wasm_types.ValueType)
          before.function.locals i1
        let n ← runtime.value.width vt
        let (r1, after) ← runtime.compiler.FunctionCompiler.copy ops before dst val n
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | .Continue _ => runtime.compiler.FunctionCompiler.observe ops after state
        | .Break residual => do
          let r2 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
            (core.convert.FromSame Itasca.error.VisitError) residual
          Result.ok (r2, after)
      | .Break residual => do
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
          (core.convert.FromSame Itasca.error.VisitError) residual
        Result.ok (r1, before)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- The live i32.const opcode casts bits and finishes a 32-bit constant. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.i32_const {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 65#u16 a b bits = (do
      let word ← lift (UScalar.cast .U32 bits)
      runtime.compiler.lower.FunctionCompiler.finish_op ops before state (.Const32 before.height word)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- The live i64.const opcode casts bits and finishes a 64-bit constant. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.i64_const {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 66#u16 a b bits = (do
      let word ← lift (UScalar.cast .U64 bits)
      runtime.compiler.lower.FunctionCompiler.finish_op ops before state (.Const64 before.height word)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- Exact live dispatcher arm for opcode 0. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.unreachable {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 0#u16 a b bits = (do
    runtime.compiler.lower.FunctionCompiler.finish_op ops before
      state runtime.bytecode.Instr.Unreachable) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- Exact live dispatcher arm for opcode 17. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.call_indirect {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 17#u16 a b bits = (do
    let i ← lift (UScalar.cast .Usize a)
    let signature ← Slice.index_usize before.signatures i
    let o ← lift (U32.checked_add signature.param_slots 1#u32)
    let r ← core.option.Option.ok_or o error.VisitError.OutOfMemory
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let o1 ← lift (U32.checked_sub before.height val)
      let r1 ← core.option.Option.ok_or o1 error.VisitError.OutOfMemory
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let (r2, self1) ←
          runtime.compiler.FunctionCompiler.pair ops before b a
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let r3 ←
            runtime.compiler.FunctionCompiler.operand ops self1
              1#usize
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            runtime.compiler.lower.FunctionCompiler.finish_op
              ops self1 state (runtime.bytecode.Instr.CallIndirect
              val2 val3 val1)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r4 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                Unit (core.convert.FromSame error.VisitError) residual
            Result.ok (r4, self1)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r3 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.VisitError) residual
          Result.ok (r3, self1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame error.VisitError) residual
        Result.ok (r2, before)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.VisitError) residual
      Result.ok (r1, before)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- Exact live dispatcher arm for opcode 35. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.global_get {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 35#u16 a b bits = (do
    let s := alloc.vec.Vec.deref state.vals
    let b1 ← runtime.compiler.lower.top_is_v128 s
    let instruction ←
      if b1
      then Result.ok (runtime.bytecode.Instr.GlobalGet2 before.height a)
      else Result.ok (runtime.bytecode.Instr.GlobalGet before.height a)
    runtime.compiler.lower.FunctionCompiler.finish_op ops before
      state instruction) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- Exact live dispatcher arm for opcode 36. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.global_set {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 36#u16 a b bits = (do
    let r ←
      runtime.compiler.FunctionCompiler.operand ops before
        1#usize
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i ← before.height - val
      let instruction ←
        if i = 2#u32
        then Result.ok (runtime.bytecode.Instr.GlobalSet2 val a)
        else Result.ok (runtime.bytecode.Instr.GlobalSet val a)
      runtime.compiler.lower.FunctionCompiler.finish_op ops
        before state instruction
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.VisitError) residual
      Result.ok (r1, before)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- Exact live dispatcher arm for opcode 37. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.table_get {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 37#u16 a b bits = (do
    let r ←
      runtime.compiler.FunctionCompiler.operand ops before
        1#usize
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        runtime.compiler.lower.FunctionCompiler.finish_op ops
          before state (runtime.bytecode.Instr.TableGet val val1 a)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame error.VisitError) residual
        Result.ok (r1, before)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.VisitError) residual
      Result.ok (r1, before)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- Exact live dispatcher arm for opcode 38. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.table_set {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 38#u16 a b bits = (do
    let r ←
      runtime.compiler.FunctionCompiler.operand ops before
        2#usize
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ←
        runtime.compiler.FunctionCompiler.operand ops before
          1#usize
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        runtime.compiler.lower.FunctionCompiler.finish_op ops
          before state (runtime.bytecode.Instr.TableSet val val1 a)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame error.VisitError) residual
        Result.ok (r2, before)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.VisitError) residual
      Result.ok (r1, before)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- Exact live dispatcher arm for opcode 63. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.memory_size {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 63#u16 a b bits = (do
    runtime.compiler.lower.FunctionCompiler.finish_op ops before
      state (runtime.bytecode.Instr.MemorySize before.height)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- Exact live dispatcher arm for opcode 64. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.memory_grow {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 64#u16 a b bits = (do
    let r ←
      runtime.compiler.FunctionCompiler.operand ops before
        1#usize
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      runtime.compiler.lower.FunctionCompiler.finish_op ops
        before state (runtime.bytecode.Instr.MemoryGrow val)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.VisitError) residual
      Result.ok (r1, before)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- Exact live dispatcher arm for opcode 67. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.f32_const {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 67#u16 a b bits = (do
    let i ← lift (UScalar.cast .U32 bits)
    runtime.compiler.lower.FunctionCompiler.finish_op ops before
      state (runtime.bytecode.Instr.Const32 before.height i)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- Exact live dispatcher arm for opcode 68. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.f64_const {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 68#u16 a b bits = (do
    let i ← lift (UScalar.cast .U64 bits)
    runtime.compiler.lower.FunctionCompiler.finish_op ops before
      state (runtime.bytecode.Instr.Const64 before.height i)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- Exact live dispatcher arm for opcode 208. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.ref_null {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 208#u16 a b bits = (do
    runtime.compiler.lower.FunctionCompiler.finish_op ops before
      state (runtime.bytecode.Instr.RefNull before.height)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- Exact live dispatcher arm for opcode 209. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.ref_is_null {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 209#u16 a b bits = (do
    let r ←
      runtime.compiler.FunctionCompiler.operand ops before
        1#usize
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        runtime.compiler.lower.FunctionCompiler.finish_op ops
          before state (runtime.bytecode.Instr.RefIsNull val val1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame error.VisitError) residual
        Result.ok (r1, before)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.VisitError) residual
      Result.ok (r1, before)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- Exact live dispatcher arm for opcode 210. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.ref_func {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 210#u16 a b bits = (do
    runtime.compiler.lower.FunctionCompiler.finish_op ops before
      state (runtime.bytecode.Instr.RefFunc before.height a)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- Exact live dispatcher arm for opcode 264. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.memory_init {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 264#u16 a b bits = (do
    let r ←
      runtime.compiler.FunctionCompiler.operand ops before
        3#usize
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      runtime.compiler.lower.FunctionCompiler.finish_op ops
        before state (runtime.bytecode.Instr.MemoryInit val a)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.VisitError) residual
      Result.ok (r1, before)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- Exact live dispatcher arm for opcode 265. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.data_drop {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 265#u16 a b bits = (do
    runtime.compiler.lower.FunctionCompiler.finish_op ops before
      state (runtime.bytecode.Instr.DataDrop a)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- Exact live dispatcher arm for opcode 266. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.memory_copy {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 266#u16 a b bits = (do
    let r ←
      runtime.compiler.FunctionCompiler.operand ops before
        3#usize
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      runtime.compiler.lower.FunctionCompiler.finish_op ops
        before state (runtime.bytecode.Instr.MemoryCopy val)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.VisitError) residual
      Result.ok (r1, before)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- Exact live dispatcher arm for opcode 267. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.memory_fill {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 267#u16 a b bits = (do
    let r ←
      runtime.compiler.FunctionCompiler.operand ops before
        3#usize
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      runtime.compiler.lower.FunctionCompiler.finish_op ops
        before state (runtime.bytecode.Instr.MemoryFill val)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.VisitError) residual
      Result.ok (r1, before)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- Exact live dispatcher arm for opcode 268. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.table_init {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 268#u16 a b bits = (do
    let (r, self1) ←
      runtime.compiler.FunctionCompiler.pair ops before a b
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ←
        runtime.compiler.FunctionCompiler.operand ops self1
          3#usize
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        runtime.compiler.lower.FunctionCompiler.finish_op ops
          self1 state (runtime.bytecode.Instr.TableInit val1 val)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame error.VisitError) residual
        Result.ok (r2, self1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.VisitError) residual
      Result.ok (r1, self1)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- Exact live dispatcher arm for opcode 269. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.elem_drop {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 269#u16 a b bits = (do
    runtime.compiler.lower.FunctionCompiler.finish_op ops before
      state (runtime.bytecode.Instr.ElemDrop a)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- Exact live dispatcher arm for opcode 270. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.table_copy {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 270#u16 a b bits = (do
    let (r, self1) ←
      runtime.compiler.FunctionCompiler.pair ops before a b
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ←
        runtime.compiler.FunctionCompiler.operand ops self1
          3#usize
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        runtime.compiler.lower.FunctionCompiler.finish_op ops
          self1 state (runtime.bytecode.Instr.TableCopy val1 val)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame error.VisitError) residual
        Result.ok (r2, self1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.VisitError) residual
      Result.ok (r1, self1)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- Exact live dispatcher arm for opcode 271. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.table_grow {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 271#u16 a b bits = (do
    let r ←
      runtime.compiler.FunctionCompiler.operand ops before
        2#usize
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      runtime.compiler.lower.FunctionCompiler.finish_op ops
        before state (runtime.bytecode.Instr.TableGrow val a)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.VisitError) residual
      Result.ok (r1, before)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- Exact live dispatcher arm for opcode 272. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.table_size {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 272#u16 a b bits = (do
    runtime.compiler.lower.FunctionCompiler.finish_op ops before
      state (runtime.bytecode.Instr.TableSize before.height a)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- Exact live dispatcher arm for opcode 273. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.table_fill {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 273#u16 a b bits = (do
    let r ←
      runtime.compiler.FunctionCompiler.operand ops before
        3#usize
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      runtime.compiler.lower.FunctionCompiler.finish_op ops
        before state (runtime.bytecode.Instr.TableFill val a)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.VisitError) residual
      Result.ok (r1, before)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true => rfl

/-- Shared live dispatcher arm for the select opcode class. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.select {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (live : before.reachable = true) (allowed : opcode = 27#u16 ∨ opcode = 28#u16) :
    runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = (do
    let r ←
      runtime.compiler.FunctionCompiler.operand ops before
        3#usize
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ←
        runtime.compiler.FunctionCompiler.operand ops before
          2#usize
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r2 ←
          runtime.compiler.FunctionCompiler.operand ops before
            1#usize
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let i ← val1 - val
          let instruction ←
            if i = 2#u32
            then Result.ok (runtime.bytecode.Instr.Select2 val val1 val2)
            else Result.ok (runtime.bytecode.Instr.Select val val1 val2)
          runtime.compiler.lower.FunctionCompiler.finish_op ops
            before state instruction
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r3 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.VisitError) residual
          Result.ok (r3, before)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame error.VisitError) residual
        Result.ok (r2, before)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.VisitError) residual
      Result.ok (r1, before)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true =>
    rcases allowed with rfl | rfl <;> rfl

/-- Shared live dispatcher arm for the memory load opcode class. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.memory_load {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (live : before.reachable = true) (allowed : 40 ≤ opcode.val ∧ opcode.val ≤ 53) :
    runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = (do
    let r ←
      runtime.compiler.FunctionCompiler.operand ops before
        1#usize
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let o ← runtime.bytecode.Instr.make_load opcode val val1 a
        let r1 ← core.option.Option.ok_or o error.VisitError.OutOfMemory
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          runtime.compiler.lower.FunctionCompiler.finish_op ops
            before state val2
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.VisitError) residual
          Result.ok (r2, before)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame error.VisitError) residual
        Result.ok (r1, before)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.VisitError) residual
      Result.ok (r1, before)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true =>
    rcases opcode with ⟨⟨value, bounds⟩⟩
    change 40 ≤ value ∧ value ≤ 53 at allowed
    obtain ⟨lo, hi⟩ := allowed
    interval_cases value <;> rfl

/-- Shared live dispatcher arm for the memory store opcode class. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.memory_store {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (live : before.reachable = true) (allowed : 54 ≤ opcode.val ∧ opcode.val ≤ 62) :
    runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = (do
    let r ←
      runtime.compiler.FunctionCompiler.operand ops before
        2#usize
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ←
        runtime.compiler.FunctionCompiler.operand ops before
          1#usize
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let o ← runtime.bytecode.Instr.make_store opcode val val1 a
        let r2 ← core.option.Option.ok_or o error.VisitError.OutOfMemory
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          runtime.compiler.lower.FunctionCompiler.finish_op ops
            before state val2
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r3 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.VisitError) residual
          Result.ok (r3, before)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame error.VisitError) residual
        Result.ok (r2, before)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.VisitError) residual
      Result.ok (r1, before)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true =>
    rcases opcode with ⟨⟨value, bounds⟩⟩
    change 54 ≤ value ∧ value ≤ 62 at allowed
    obtain ⟨lo, hi⟩ := allowed
    interval_cases value <;> rfl

/-- Shared live dispatcher arm for the scalar opcode class. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.scalar {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (live : before.reachable = true) (allowed : (69 ≤ opcode.val ∧ opcode.val ≤ 196) ∨ (256 ≤ opcode.val ∧ opcode.val ≤ 263)) :
    runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = (do
    let b1 ← runtime.compiler.lower.scalar_binary opcode
    let depth ← if b1
                  then Result.ok 2#usize
                  else Result.ok 1#usize
    let r ←
      runtime.compiler.FunctionCompiler.operand ops before depth
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ←
        runtime.compiler.FunctionCompiler.operand ops before
          1#usize
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let o ← runtime.bytecode.Instr.make_scalar opcode val val val1
        let r2 ← core.option.Option.ok_or o error.VisitError.OutOfMemory
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          runtime.compiler.lower.FunctionCompiler.finish_op ops
            before state val2
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r3 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.VisitError) residual
          Result.ok (r3, before)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame error.VisitError) residual
        Result.ok (r2, before)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.VisitError) residual
      Result.ok (r1, before)) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true =>
    rcases opcode with ⟨⟨value, bounds⟩⟩
    change (69 ≤ value ∧ value ≤ 196) ∨ (256 ≤ value ∧ value ≤ 263) at allowed
    rcases allowed with ⟨lo, hi⟩ | ⟨lo, hi⟩ <;> interval_cases value <;> rfl

private theorem op_simd_low {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (live : before.reachable = true) (allowed : 512 ≤ opcode.val ∧ opcode.val ≤ 639) :
    runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = (do
    runtime.compiler.simd.FunctionCompiler.simd_op ops before state
      opcode a bits) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true =>
    rcases opcode with ⟨⟨value, bounds⟩⟩
    change 512 ≤ value ∧ value ≤ 639 at allowed
    obtain ⟨lo, hi⟩ := allowed
    interval_cases value <;> rfl

private theorem op_simd_high {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (live : before.reachable = true) (allowed : 640 ≤ opcode.val ∧ opcode.val ≤ 767) :
    runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = (do
    runtime.compiler.simd.FunctionCompiler.simd_op ops before state
      opcode a bits) := by
  rcases before with ⟨signatures, slots, budget, start, fn, frames, reachable, next, operands, height, offsets, depths⟩
  cases reachable with
  | false => cases live
  | true =>
    rcases opcode with ⟨⟨value, bounds⟩⟩
    change 640 ≤ value ∧ value ≤ 767 at allowed
    obtain ⟨lo, hi⟩ := allowed
    interval_cases value <;> rfl

/-- Shared live dispatcher arm for the simd opcode class. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.simd {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (live : before.reachable = true) (allowed : 512 ≤ opcode.val ∧ opcode.val ≤ 767) :
    runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = (do
    runtime.compiler.simd.FunctionCompiler.simd_op ops before state
      opcode a bits) := by
  by_cases lowerHalf : opcode.val ≤ 639
  · exact op_simd_low ops before state opcode a b bits live ⟨allowed.1, lowerHalf⟩
  · exact op_simd_high ops before state opcode a b bits live ⟨by omega, allowed.2⟩

/-- Shared live local.set/local.tee dispatcher arm. -/
theorem _root_.Itasca.runtime.compiler.lower.FunctionCompiler.op.local_set_or_tee {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (tee : Bool) (a b : U32) (bits : U128)
    (live : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state (if tee then 34#u16 else 33#u16) a b bits = (do
      let i ← lift (UScalar.cast .Usize a)
      let dst ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) before.local_offsets i
      let r ← runtime.compiler.FunctionCompiler.operand ops before 1#usize
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | .Continue val => do
        let i1 ← lift (UScalar.cast .Usize a)
        let vt ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Itasca.wasm_types.ValueType)
          before.function.locals i1
        let n ← runtime.value.width vt
        let (r1, after) ← runtime.compiler.FunctionCompiler.copy ops before dst val n
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | .Continue _ => runtime.compiler.FunctionCompiler.observe ops after state
        | .Break residual => do
          let r2 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
            (core.convert.FromSame Itasca.error.VisitError) residual
          Result.ok (r2, after)
      | .Break residual => do
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
          (core.convert.FromSame Itasca.error.VisitError) residual
        Result.ok (r1, before)) := by
  cases tee with
  | false => exact runtime.compiler.lower.FunctionCompiler.op.local_set ops before state a b bits live
  | true => exact runtime.compiler.lower.FunctionCompiler.op.local_tee ops before state a b bits live

end Itasca.Runtime.Compiler
