import Itasca.Runtime.Compiler.Local.Checking.ScalarExitSlotBounds
import Itasca.Runtime.Compiler.Body.Reader.Scalar.Emissions
import Itasca.Runtime.Compiler.Body.Reader.Float.FloatConstantEmissions
import Itasca.Runtime.Compiler.Body.Reader.Replay.OrdinaryEffects
import Itasca.Runtime.Compiler.Local.Checking.LinearEmissionInstructionPrefix
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.ScalarAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Publication.ScalarCallbackPublication
import Itasca.Runtime.Compiler.Local.Checking.DeadInstructionPrefix
import Itasca.Runtime.Compiler.Local.Checking.TerminalInstructionPrefix
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Checking.NoopInstructionPrefix
import Itasca.Runtime.Compiler.Body.Reader.Checking.CoreInstructionPrefix
import Itasca.Runtime.Compiler.Body.Reader.Control.TerminalInstructionPrefix

/-!
Checked prefixes for constants, nop/drop and dormant scalar reader cases, composed into complete-profile scalar instruction checking.
-/

/-! ## Reader Constant Instruction Prefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual typed literal reading checks its emitted word and retains earlier checks. -/
theorem reader_const32_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List wasm_types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
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
  exact ⟨lowered.1.linear_instruction_prefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual typed literal reading checks its emitted word and retains earlier checks. -/
theorem reader_const64_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List wasm_types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
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
  exact ⟨lowered.1.linear_instruction_prefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual typed literal reading checks its emitted word and retains earlier checks. -/
theorem reader_float32_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A)
    (C : context) (localTypes : C.LOCALS = compilerLocals before) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List wasm_types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
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
  exact ⟨lowered.1.float_core_instruction_prefix layout reachable localTypes emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual typed literal reading checks its emitted word and retains earlier checks. -/
theorem reader_float64_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A)
    (C : context) (localTypes : C.LOCALS = compilerLocals before) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List wasm_types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
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
  exact ⟨lowered.1.float_core_instruction_prefix layout reachable localTypes emission tables held stable.frames,stable.exit_slots exits⟩

end Itasca.Runtime.Compiler

end

/-! ## Reader Dead Scalar Instruction Prefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- All scalar source reader kinds preserve both checks in unreachable code.
Literal bits and local/global indices are exactly those selected by the reader. -/
theorem reader_dead_scalar_checked_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (kind : ScalarReaderKind)
    (dead : before.reachable = false)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx kind.opcode before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  rw [kind.dispatch] at accepted
  obtain ⟨value,_,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
  by_cases trap : kind = .unreachable
  · subst kind
    exact ⟨compiler_unreachable_open_instructions ops law before after out codeFits sourceFits coordinateFits held callback,
      (compiler_unreachable_ordinary_result ops law before after out (.Ok ()) callback).exit_slots exits⟩
  · have supported : ScalarPublicationAction (kind.action value) := by
      cases kind <;> first | contradiction | constructor
    obtain ⟨opcode,a,b,bits,_,dispatch⟩ := scalar_hook_publication_dispatch ops before out supported
    rw [dispatch] at callback
    exact compiler_dead_op_checked_prefix ops law before after out opcode a b bits dead held exits callback

end Itasca.Runtime.Compiler

end

/-! ## Reader Noop Instruction Prefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Actual nop reading preserves instruction and recorded exit-slot checks. -/
theorem reader_nop_open_instructions_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 1#u8 before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 1#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_nop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ run
  cases value
  exact compiler_nop_drop_open_instructions ops law before after out.core false held exits callback

/-- Actual drop reading preserves instruction and recorded exit-slot checks. -/
theorem reader_drop_open_instructions_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 26#u8 before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 26#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_drop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ run
  exact compiler_nop_drop_open_instructions ops law before after out.core true held exits callback

end Itasca.Runtime.Compiler

end

/-! ## Reader Scalar Instruction Prefix Wasm2 -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Every scalar reader kind preserves both instruction and recorded exit-slot
checks from its source-typed prefix, including all unreachable variants. -/
theorem reader_scalar_checked_prefix_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (contextSource : ctx.locals = sourceLocals) (C : context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (localsMatch : before.function.locals = sourceLocals)
    (contextLocals : C.LOCALS = locals)
    (globalsMatch : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (kind : ScalarReaderKind) (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = kind.opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 kind.opcode before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  have sourcePosition : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities sourcePosition
  have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  by_cases live : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live live
    have known := invariant.known live
    have layout := retained.layout
    have localTypes : C.LOCALS = compilerLocals before := contextLocals.trans retained.localsEq.symm
    obtain ⟨rawTypes,concrete⟩ := (concrete_stack_iff st.core.vals.val).mp known
    have literalLayout : CompilerLayout before (rawTypes.map Translate.valueType) := by
      simpa only [concrete,Sequence.stackTypes,List.map_map,Function.comp_def] using layout
    cases kind with
    | nop =>
      exact reader_nop_open_instructions_wasm2 ops law before after st out data env ctx index held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | unreachable =>
      exact reader_unreachable_open_instructions_wasm2 p ops law initial before after out ctx contextSource invariant held exits bodyBound (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | drop =>
      exact reader_drop_open_instructions_wasm2 ops law before after st out data env ctx index held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | select =>
      exact reader_select_open_instructions_wasm2 p ops law before after out ctx contextSource C localTypes.symm known (monomorphic live) layout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | local_get =>
      exact reader_local_get_open_instructions_wasm2 p ops law before after out ctx contextSource localsMatch rawTypes concrete literalLayout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | local_set =>
      exact reader_local_set_open_instructions_wasm2 p ops law before after out ctx contextSource localsMatch known (monomorphic live) layout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | local_tee =>
      exact reader_local_tee_open_instructions_wasm2 p ops law before after out ctx contextSource localsMatch known (monomorphic live) layout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | global_get =>
      exact reader_global_get_open_instructions_wasm2 p ops law before after out ctx contextSource C localTypes.symm globalsMatch rawTypes concrete literalLayout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | global_set =>
      exact reader_global_set_open_instructions_wasm2 p ops law before after out ctx contextSource C localTypes.symm globalsMatch known (monomorphic live) layout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | i32_const =>
      exact reader_const32_open_instructions_wasm2 p ops law before after out ctx contextSource rawTypes concrete literalLayout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | i64_const =>
      exact reader_const64_open_instructions_wasm2 p ops law before after out ctx contextSource rawTypes concrete literalLayout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | f32_const =>
      exact reader_float32_open_instructions_wasm2 p ops law before after C localTypes out ctx contextSource rawTypes concrete literalLayout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | f64_const =>
      exact reader_float64_open_instructions_wasm2 p ops law before after C localTypes out ctx contextSource rawTypes concrete literalLayout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
  · obtain ⟨_,raw⟩ := profile_base_success_wasm2
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index kind.opcode before after
      kind.ordinary kind.plain kind.sign kind.misc rfl accepted
    exact reader_dead_scalar_checked_prefix ops law before after st.core out.core data env ctx kind
      (Bool.eq_false_iff.mpr live) codeFits sourceFits coordinateFits held exits raw

end Itasca.Runtime.Compiler

end
