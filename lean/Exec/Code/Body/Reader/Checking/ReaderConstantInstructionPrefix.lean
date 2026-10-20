import Exec.Code.Local.Checking.ScalarExitSlotBounds
import Exec.Code.Body.Reader.Common.ReaderEmissions
import Exec.Code.Body.Reader.Float.ReaderFloatConstantEmissions
import Exec.Code.Body.Reader.Table.ReaderLiteralTables
import Exec.Code.Body.Reader.Table.ReaderLiteralTablesWasm1
import Exec.Code.Body.Reader.Table.ReaderCoreTables
import Exec.Code.Body.Reader.Table.ReaderCoreTablesWasm1
import Exec.Code.Local.Checking.LinearEmissionInstructionPrefix

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Actual typed literal reading checks its emitted word and retains earlier checks. -/
theorem reader_const32_open_instructions_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (types : List types.ValueType) (concrete : st.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I32_CONST)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_I32_CONST before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,value,post,instruction,lowered,emission⟩ :=
    reader_emit_const32_wasm1 p ops law before after out types concrete layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := reader_i32_const_tables_wasm1 ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  exact ⟨lowered.1.linearInstructionPrefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual typed literal reading checks its emitted word and retains earlier checks. -/
theorem reader_const64_open_instructions_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (types : List types.ValueType) (concrete : st.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I64_CONST)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_I64_CONST before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,value,post,instruction,lowered,emission⟩ :=
    reader_emit_const64_wasm1 p ops law before after out types concrete layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := reader_i64_const_tables_wasm1 ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  exact ⟨lowered.1.linearInstructionPrefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual typed literal reading checks its emitted word and retains earlier checks. -/
theorem reader_float32_open_instructions_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A)
    (C : context) (localTypes : C.LOCALS = compilerLocals before) (out : code.OpIterState)
    (types : List types.ValueType) (concrete : st.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F32_CONST)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_F32_CONST before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,value,post,instruction,lowered,emission⟩ :=
    reader_emit_float32_wasm1 p ops law before after C localTypes out types concrete layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := reader_f32_const_tables_wasm1 ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  exact ⟨lowered.1.floatCoreInstructionPrefix layout reachable localTypes (.core emission) tables held stable.frames,stable.exit_slots exits⟩

/-- Actual typed literal reading checks its emitted word and retains earlier checks. -/
theorem reader_float64_open_instructions_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A)
    (C : context) (localTypes : C.LOCALS = compilerLocals before) (out : code.OpIterState)
    (types : List types.ValueType) (concrete : st.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F64_CONST)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_F64_CONST before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,value,post,instruction,lowered,emission⟩ :=
    reader_emit_float64_wasm1 p ops law before after C localTypes out types concrete layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := reader_f64_const_tables_wasm1 ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  exact ⟨lowered.1.floatCoreInstructionPrefix layout reachable localTypes (.core emission) tables held stable.frames,stable.exit_slots exits⟩

/-- Actual typed literal reading checks its emitted word and retains earlier checks. -/
theorem reader_const32_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
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
  have tables := reader_i32_const_tables_wasm2 ops law before after st out data env ctx index (by simpa only [global_simps] using accepted)
  exact ⟨lowered.1.linearInstructionPrefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual typed literal reading checks its emitted word and retains earlier checks. -/
theorem reader_const64_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
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
  have tables := reader_i64_const_tables_wasm2 ops law before after st out data env ctx index (by simpa only [global_simps] using accepted)
  exact ⟨lowered.1.linearInstructionPrefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual typed literal reading checks its emitted word and retains earlier checks. -/
theorem reader_float32_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
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
  have tables := reader_f32_const_tables_wasm2 ops law before after st out data env ctx index (by simpa only [global_simps] using accepted)
  exact ⟨lowered.1.floatCoreInstructionPrefix layout reachable localTypes (.core emission) tables held stable.frames,stable.exit_slots exits⟩

/-- Actual typed literal reading checks its emitted word and retains earlier checks. -/
theorem reader_float64_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
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
  have tables := reader_f64_const_tables_wasm2 ops law before after st out data env ctx index (by simpa only [global_simps] using accepted)
  exact ⟨lowered.1.floatCoreInstructionPrefix layout reachable localTypes (.core emission) tables held stable.frames,stable.exit_slots exits⟩

end Exec.Code
