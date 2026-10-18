import Exec.Code.Local.Lowering.Common.Lowering
/-! Actual integer-add callbacks preserve the source-prefix lowering relation.
Operand addresses come from the compiler's live layout; the proof then follows
the extracted opcode classifier, constructor, emitter, and post-stack observer. -/

namespace Exec.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096 in
theorem lower_add32_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (left right : U32) (reachable : compiler.reachable = true)
    (hleft : runtime.compiler.FunctionCompiler.operand ops compiler 2#usize = .ok (.Ok left))
    (hright : runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok right)) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 106#u16 0#u32 0#u32 0#u128 =
      runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state (.I32Add left left right) := by
  have binary : runtime.compiler.lower.scalar_binary 106#u16 = .ok true := by rfl
  have make (a b : U32) : runtime.bytecode.Instr.make_scalar 106#u16 a a b =
      .ok (some (.I32Add a a b)) := by rfl
  have run : runtime.compiler.lower.FunctionCompiler.op ops compiler state 106#u16 0#u32 0#u32 0#u128 = (do
    let binary ← runtime.compiler.lower.scalar_binary 106#u16
    let depth ← if binary
                  then Result.ok 2#usize
                  else Result.ok 1#usize
    let r ←
      runtime.compiler.FunctionCompiler.operand ops compiler depth
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ←
        runtime.compiler.FunctionCompiler.operand ops compiler
          1#usize
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let o ← runtime.bytecode.Instr.make_scalar 106#u16 val val val1
        let r2 ←
          core.option.Option.ok_or o
            _root_.Itasca.error.VisitError.OutOfMemory
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          runtime.compiler.lower.FunctionCompiler.finish_op ops
            compiler state val2
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r3 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
              residual
          Result.ok (r3, compiler)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
            residual
        Result.ok (r2, compiler)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
          residual
      Result.ok (r1, compiler)) := by
    unfold runtime.compiler.lower.FunctionCompiler.op
    rewrite [if_pos reachable]
    rfl
  rewrite [run, binary, bind_ok]
  simp only [ite_true, bind_ok, hleft, hright,
    core.result.Result.Insts.CoreOpsTry.branch, make, core.option.Option.ok_or]
set_option maxRecDepth 4096 in
theorem lower_add64_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (left right : U32) (reachable : compiler.reachable = true)
    (hleft : runtime.compiler.FunctionCompiler.operand ops compiler 2#usize = .ok (.Ok left))
    (hright : runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok right)) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 124#u16 0#u32 0#u32 0#u128 =
      runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state (.I64Add left left right) := by
  have binary : runtime.compiler.lower.scalar_binary 124#u16 = .ok true := by rfl
  have make (a b : U32) : runtime.bytecode.Instr.make_scalar 124#u16 a a b =
      .ok (some (.I64Add a a b)) := by rfl
  have run : runtime.compiler.lower.FunctionCompiler.op ops compiler state 124#u16 0#u32 0#u32 0#u128 = (do
    let binary ← runtime.compiler.lower.scalar_binary 124#u16
    let depth ← if binary
                  then Result.ok 2#usize
                  else Result.ok 1#usize
    let r ←
      runtime.compiler.FunctionCompiler.operand ops compiler depth
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ←
        runtime.compiler.FunctionCompiler.operand ops compiler
          1#usize
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let o ← runtime.bytecode.Instr.make_scalar 124#u16 val val val1
        let r2 ←
          core.option.Option.ok_or o
            _root_.Itasca.error.VisitError.OutOfMemory
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          runtime.compiler.lower.FunctionCompiler.finish_op ops
            compiler state val2
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r3 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
              residual
          Result.ok (r3, compiler)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
            residual
        Result.ok (r2, compiler)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
          residual
      Result.ok (r1, compiler)) := by
    unfold runtime.compiler.lower.FunctionCompiler.op
    rewrite [if_pos reachable]
    rfl
  rewrite [run, binary, bind_ok]
  simp only [ite_true, bind_ok, hleft, hright,
    core.result.Result.Insts.CoreOpsTry.branch, make, core.option.Option.ok_or]

theorem binary_operands {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (front : List valtype) (ty : Inn)
    (layout : CompilerLayout compiler (front ++ [integerType ty, integerType ty])) :
    ∃ left right : U32,
      runtime.compiler.FunctionCompiler.operand ops compiler 2#usize = .ok (.Ok left) ∧
      runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok right) ∧
      left.val = slots (compilerLocals compiler) + slots front ∧ right.val = left.val + 1 := by
  obtain ⟨r, hr, left, rfl, hl⟩ := WP.spec_imp_exists
    (compiler_operand ops compiler _ layout 2#usize (by decide) (by simp))
  obtain ⟨r, hr', right, rfl, hh⟩ := WP.spec_imp_exists
    (compiler_operand ops compiler _ layout 1#usize (by decide) (by simp))
  have leftPos : left.val = slots (compilerLocals compiler) + slots front := by
    simpa [offset, List.take_append] using hl
  have rightPos : right.val = left.val + 1 := by
    have take : front.take (front.length + 1) = front := List.take_of_length_le (by omega)
    rw [leftPos]
    cases ty <;> simpa [offset, List.take_append, slots_append, slots, width, integerType, take,
      Nat.add_assoc] using hh
  exact ⟨left, right, hr, hr', leftPos, rightPos⟩

@[step] theorem callback_add32_certificate {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (front : List valtype)
    (layout : CompilerLayout compiler (front ++ [.I32, .I32]))
    (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ [.I32])
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_add ops compiler state ⦃ out =>
      out.1 = .Ok () →
        LinearCodeRel (compilerLocals compiler) (front ++ [.I32, .I32])
          [IntegerBinary.add.source .I32] out.2.function.code.val
          compiler.function.code.val.length (compiler.function.code.val.length + 1) (front ++ [.I32]) ∧
        CompilerLayout out.2 (front ++ [.I32]) ⦄ := by
  obtain ⟨left, right, hl, hr, hleft, hright⟩ := binary_operands ops compiler front .I32 layout
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_add
  rw [lower_add32_eq ops compiler state left right reachable hl hr]
  step with finish_op ops law compiler state types (.I32Add left left right) _ layout concrete
    codeFits sourceFits coordinateFits as ⟨out, hout, success⟩
  have lowered := hout success
  rw [typed] at lowered
  exact ⟨lowered.linear_code (LinearEmission.binary front .I32 .add left right hleft hright),
    lowered.2.1⟩

@[step] theorem callback_add64_certificate {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (front : List valtype)
    (layout : CompilerLayout compiler (front ++ [.I64, .I64]))
    (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ [.I64])
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_add ops compiler state ⦃ out =>
      out.1 = .Ok () →
        LinearCodeRel (compilerLocals compiler) (front ++ [.I64, .I64])
          [IntegerBinary.add.source .I64] out.2.function.code.val
          compiler.function.code.val.length (compiler.function.code.val.length + 1) (front ++ [.I64]) ∧
        CompilerLayout out.2 (front ++ [.I64]) ⦄ := by
  obtain ⟨left, right, hl, hr, hleft, hright⟩ := binary_operands ops compiler front .I64 layout
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_add
  rw [lower_add64_eq ops compiler state left right reachable hl hr]
  step with finish_op ops law compiler state types (.I64Add left left right) _ layout concrete
    codeFits sourceFits coordinateFits as ⟨out, hout, success⟩
  have lowered := hout success
  rw [typed] at lowered
  exact ⟨lowered.linear_code (LinearEmission.binary front .I64 .add left right hleft hright),
    lowered.2.1⟩

@[step] theorem callback_add32_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (front : List valtype)
    (locals initial : List valtype) (source : List instr)
    (inv : LinearCompileInv compiler locals initial source (front ++ [.I32, .I32]))
    (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ [.I32])
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_add ops compiler state ⦃ out =>
      out.1 = .Ok () →
        LinearCompileInv out.2 locals initial
          (source ++ [IntegerBinary.add.source .I32]) (front ++ [.I32]) ⦄ := by
  have layout := inv.layout
  obtain ⟨left, right, hl, hr, hleft, hright⟩ := binary_operands ops compiler front .I32 layout
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_add
  rw [lower_add32_eq ops compiler state left right reachable hl hr]
  step with finish_op ops law compiler state types (.I32Add left left right) _ layout concrete
    codeFits sourceFits coordinateFits as ⟨out, hout, success⟩
  have lowered := hout success
  rw [typed] at lowered
  apply lowered.extend_prefix inv
  apply LinearEmission.binary front .I32 .add left right
  · simpa [inv.localsEq] using hleft
  · exact hright


@[step] theorem callback_add64_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (front : List valtype)
    (locals initial : List valtype) (source : List instr)
    (inv : LinearCompileInv compiler locals initial source (front ++ [.I64, .I64]))
    (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ [.I64])
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_add ops compiler state ⦃ out =>
      out.1 = .Ok () →
        LinearCompileInv out.2 locals initial
          (source ++ [IntegerBinary.add.source .I64]) (front ++ [.I64]) ⦄ := by
  have layout := inv.layout
  obtain ⟨left, right, hl, hr, hleft, hright⟩ := binary_operands ops compiler front .I64 layout
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_add
  rw [lower_add64_eq ops compiler state left right reachable hl hr]
  step with finish_op ops law compiler state types (.I64Add left left right) _ layout concrete
    codeFits sourceFits coordinateFits as ⟨out, hout, success⟩
  have lowered := hout success
  rw [typed] at lowered
  apply lowered.extend_prefix inv
  apply LinearEmission.binary front .I64 .add left right
  · simpa [inv.localsEq] using hleft
  · exact hright


end Exec.Code
