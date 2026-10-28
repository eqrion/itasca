import Exec.Code.Local.Checking.ScalarExitSlotBounds
import Exec.Code.Body.Reader.Common.ReaderEmissions
import Exec.Code.Body.Reader.Float.ReaderFloatConstantEmissions
import Exec.Code.Body.Reader.Common.ReaderOrdinaryEffects
import Exec.Code.Local.Checking.LinearEmissionInstructionPrefix

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Actual typed literal reading checks its emitted word and retains earlier checks. -/
theorem reader_const32_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I32_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_I32_CONST before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,value,post,instruction,lowered,emission⟩ :=
    reader_emit_const32_wasm2 p ops law before after out ctx contextLocals types concrete layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_i32_const_effects ops law before after st.core out.core data env ctx
    (base_step_wasm2 _ (by decide) (by decide) rfl (by simp only [global_simps]; decide) (by simpa only [global_simps] using accepted))).tables
  exact ⟨lowered.1.linearInstructionPrefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual typed literal reading checks its emitted word and retains earlier checks. -/
theorem reader_const64_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I64_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_I64_CONST before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,value,post,instruction,lowered,emission⟩ :=
    reader_emit_const64_wasm2 p ops law before after out ctx contextLocals types concrete layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_i64_const_effects ops law before after st.core out.core data env ctx
    (base_step_wasm2 _ (by decide) (by decide) rfl (by simp only [global_simps]; decide) (by simpa only [global_simps] using accepted))).tables
  exact ⟨lowered.1.linearInstructionPrefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual typed literal reading checks its emitted word and retains earlier checks. -/
theorem reader_float32_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A)
    (C : context) (localTypes : C.LOCALS = compilerLocals before) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F32_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_F32_CONST before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,value,post,instruction,lowered,emission⟩ :=
    reader_emit_float32_wasm2 p ops law before after C localTypes out ctx contextLocals types concrete layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_f32_const_effects ops law before after st.core out.core data env ctx
    (base_step_wasm2 _ (by decide) (by decide) rfl (by simp only [global_simps]; decide) (by simpa only [global_simps] using accepted))).tables
  exact ⟨lowered.1.floatCoreInstructionPrefix layout reachable localTypes emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual typed literal reading checks its emitted word and retains earlier checks. -/
theorem reader_float64_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A)
    (C : context) (localTypes : C.LOCALS = compilerLocals before) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F64_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_F64_CONST before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,value,post,instruction,lowered,emission⟩ :=
    reader_emit_float64_wasm2 p ops law before after C localTypes out ctx contextLocals types concrete layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_f64_const_effects ops law before after st.core out.core data env ctx
    (base_step_wasm2 _ (by decide) (by decide) rfl (by simp only [global_simps]; decide) (by simpa only [global_simps] using accepted))).tables
  exact ⟨lowered.1.floatCoreInstructionPrefix layout reachable localTypes emission tables held stable.frames,stable.exit_slots exits⟩

end Itasca.Runtime.Code
