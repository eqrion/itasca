import Itasca.Runtime.Compiler.Local.Checking.LoopBranchInstructionPrefix
import Itasca.Runtime.Compiler.Body.Reader.Scalar.Unreachable
import Itasca.Runtime.Compiler.Body.Reader.Float.FloatConstantEmissions
import Itasca.Runtime.Compiler.Body.Reader.Replay.OrdinaryEffects
import Itasca.Runtime.Compiler.Local.Checking.ScopeEntryInstructionPrefix
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.RecordedAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Publication.ScalarCallbackPublication
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Body.Reader.Checking.OperationInstructionPrefix
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTablePublication
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixFinish
import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedFullCapacity
import Itasca.Runtime.Compiler.Body.Relations.Checking.ExecutableInstructionPrefix
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableScratchLiteral
import Itasca.Runtime.Compiler.Local.Relations.Table.StatefulAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Lowering.Table.ScalarTablePreservation
import Itasca.Runtime.Compiler.Body.Reader.References.TypedSelectEmission
import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulBase
import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulBulkDispatch
import Itasca.Runtime.Compiler.Body.Reader.Replay.BulkAndSaturatingAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Source.SourceOpcodeFamilies
import Itasca.Runtime.Compiler.Body.Reader.Simd.Dispatch
import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdInstructionPrefix
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPreserved

/-!
Sections, each formerly its own module: ScalarInstructionPrefixWasm2, StatefulInstructionPrefix, TypedSelectCheckedPrefix, NoncontrolCheckedPrefixWasm2, CheckedPrefixWasm2.
-/

/-! ## ScalarInstructionPrefixWasm2 -/

section

/-!
Checked prefixes for constants, nop/drop and dormant scalar reader cases, composed into complete-profile scalar instruction checking.
-/

/-! ## Reader Constant Instruction Prefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual typed literal reading checks its emitted word and retains earlier checks. -/
theorem reader_const32_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
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
      st data env ctx index code.OP_I32_CONST before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,value,post,instruction,lowered,emission⟩ :=
    reader_emit_const32_wasm2 p ops law before after out ctx contextLocals types concrete layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_i32_const_effects ops law before after st.core out.core data env ctx
    (base_step_wasm2 _ (by decide) (by decide) rfl (by simp only [global_simps]; decide) (by simpa only [global_simps] using accepted))).tables
  exact ⟨lowered.1.linear_instruction_prefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual typed literal reading checks its emitted word and retains earlier checks. -/
theorem reader_const64_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
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
      st data env ctx index code.OP_I64_CONST before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,value,post,instruction,lowered,emission⟩ :=
    reader_emit_const64_wasm2 p ops law before after out ctx contextLocals types concrete layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_i64_const_effects ops law before after st.core out.core data env ctx
    (base_step_wasm2 _ (by decide) (by decide) rfl (by simp only [global_simps]; decide) (by simpa only [global_simps] using accepted))).tables
  exact ⟨lowered.1.linear_instruction_prefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual typed literal reading checks its emitted word and retains earlier checks. -/
theorem reader_float32_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
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
      st data env ctx index code.OP_F32_CONST before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,value,post,instruction,lowered,emission⟩ :=
    reader_emit_float32_wasm2 p ops law before after C localTypes out ctx contextLocals types concrete layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_f32_const_effects ops law before after st.core out.core data env ctx
    (base_step_wasm2 _ (by decide) (by decide) rfl (by simp only [global_simps]; decide) (by simpa only [global_simps] using accepted))).tables
  exact ⟨lowered.1.float_core_instruction_prefix layout reachable localTypes emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual typed literal reading checks its emitted word and retains earlier checks. -/
theorem reader_float64_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
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
      st data env ctx index code.OP_F64_CONST before = .ok (.Ok (), out, after)) :
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
      st data env ctx index 1#u8 before = .ok (.Ok (),out,after)) :
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
      st data env ctx index 26#u8 before = .ok (.Ok (),out,after)) :
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
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
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
      st data env ctx index kind.opcode before = .ok (.Ok (),out,after)) :
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

end

/-! ## StatefulInstructionPrefix -/

section

/-!
Source-typed stateful metadata readers check every newly emitted word and retain both pending instruction checks and the slots of recorded exits.

Main declarations: `StatefulReaderPost.instruction_prefix`. A direct consumer is `Compiler.Body.Reader.Checking.NoncontrolCheckedPrefixWasm2`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Source-typed stateful metadata readers check every newly emitted word and
retain both pending instruction checks and the slots of recorded exits. -/
theorem StatefulReaderPost.instruction_prefix {jumpTables : List U32} {data env sourceLocals index st}
    {p : Wasm2.Pending data env sourceLocals index st} {out : code.OpIterState} {op : SourceMachine.Stateful.Instruction}
    (post : StatefulReaderPost p out op) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (C : context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (matched : EnvTranslation.Matches env ⟨sourceLocals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (a b : U32) (arguments : StatefulArguments op a b)
    (callback : runtime.compiler.lower.FunctionCompiler.op ops before out (statefulOpcode op) a b 0#u128 = .ok (.Ok (),after))
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  cases reachable : before.reachable with
  | false =>
    have checked := compiler_dead_op_open_instructions ops law before after out (statefulOpcode op) a b 0#u128
      reachable held callback
    unfold runtime.compiler.lower.FunctionCompiler.op at callback
    rw [if_neg (by simp [reachable])] at callback
    exact ⟨checked,compiler_observe_exit_slots ops law before after out exits callback⟩
  | true =>
    obtain ⟨entered,retained⟩ := invariant.live reachable
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    obtain ⟨ordinary,sources,cursor,⟨extra,pairs⟩,values,emitted,output,reader,lowered,emission⟩ :=
      post.emission ops law before after C a b arguments callback matched
        (contextLocals.trans retained.localsEq.symm) (invariant.known reachable) (monomorphic reachable)
        retained.layout reachable codeFits sourceFits coordinateFits
    have tables := compiler_tables_pair_append before.function after.function extra pairs
      (compiler_stateful_auxiliary_tables ops law before after out op a b (.Ok ()) callback)
    have growth := instruction_check_extends_of_tables_append before.function after.function _ tables
      ordinary.capacity (by change before.function.code.val.length ≤ after.function.code.val.length; rw [lowered.1.1,List.length_append,List.length_singleton]; omega)
    exact ⟨lowered.1.executable_instruction_prefix retained.layout reachable (contextLocals.trans retained.localsEq.symm)
      (.stateful emission) emission.not_branch_table growth held ordinary.frames,
      exits.retained (congrArg alloc.vec.Vec.val ordinary.frames) ordinary.capacity⟩

end Itasca.Runtime.Compiler

end

/-! ## TypedSelectCheckedPrefix -/

section

/-!
Open-instruction and checked-prefix preservation for typed-select reader steps.
-/

/-! ## Reader Typed Select Instruction Prefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual typed select uses the source-selected width for its instruction check. -/
theorem reader_typed_select_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (C : context) (localsMatch : compilerLocals before = C.LOCALS)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 28#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 28#u8 before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,ty,front,values,emitted,input,post,lowered,emission⟩ :=
    reader_emit_typed_select_wasm2 p ops law before after out ctx C localsMatch known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  obtain ⟨other,position,callback,_⟩ := reader_typed_select_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 28#u16 0#u32 0#u32 0#u128 = _ at callback
  have tables := compiler_core_tables ops law before after out.core (.select true) callback
  have growth := lowered.1.instruction_check_extends tables
  rw [input] at layout
  exact ⟨lowered.1.executable_instruction_prefix layout reachable localsMatch.symm
    (.typedSelect emission) (by intro depths fallback same; cases same) growth held stable.frames,
    exits.retained (congrArg alloc.vec.Vec.val stable.frames) stable.capacity⟩

end Itasca.Runtime.Compiler

end

/-! ## Reader Typed Select Checked Prefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Typed select preserves both invariants for either source reachability bit;
only live source code emits the selected-width instruction. -/
theorem reader_typed_select_checked_prefix_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (C : context) (contextLocals : C.LOCALS = locals)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 28#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 28#u8 before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  by_cases live : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live live
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    exact reader_typed_select_open_instructions_wasm2 p ops law before after out ctx C
      (retained.localsEq.trans contextLocals.symm) (invariant.known live) (monomorphic live) retained.layout live
      codeFits sourceFits coordinateFits held exits byte accepted
  · obtain ⟨ty,position,callback,_⟩ := reader_typed_select_wasm2 p
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
    change runtime.compiler.lower.FunctionCompiler.op ops before out.core 28#u16 0#u32 0#u32 0#u128 = _ at callback
    exact compiler_dead_op_checked_prefix ops law before after out.core 28#u16 0#u32 0#u32 0#u128
      (Bool.eq_false_iff.mpr live) held exits callback

end Itasca.Runtime.Compiler

end

end

/-! ## NoncontrolCheckedPrefixWasm2 -/

section

/-!
Source opcode coverage composes every noncontrol Wasm 2 reader family, including unreachable code, bulk operations, typed select, and all SIMD forms. The excluded control cases have separate source-frame adapters.

Main declarations: `reader_noncontrol_checked_prefix_wasm2`. A direct consumer is `Compiler.Body.Reader.Checking.CheckedPrefixWasm2`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Source opcode coverage composes every noncontrol Wasm 2 reader family,
including unreachable code, bulk operations, typed select, and all SIMD forms.
The excluded control cases have separate source-frame adapters. -/
theorem reader_noncontrol_checked_prefix_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (contextSource : ctx.locals = sourceLocals) (C : context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (localsMatch : before.function.locals = sourceLocals)
    (matched : EnvTranslation.Matches env ⟨sourceLocals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (opcode : U8) (noncontrol : opcode.val ∉ [2,3,4,5,11,12,13,14,15,16,17])
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index opcode before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  cases source_opcode_family opcode with
  | scalar kind same =>
    rw [same] at byte accepted noncontrol
    exact reader_scalar_checked_prefix_wasm2 p ops law initial before after out ctx contextSource C invariant localsMatch
      contextLocals matched.globals monomorphic sourceBound bodyBound kind held exits byte accepted
  | integer op base same =>
    rw [same] at byte accepted noncontrol
    exact reader_numeric_checked_prefix_wasm2 p ops law initial before after out ctx contextSource invariant
      monomorphic sourceBound bodyBound op base held exits byte accepted
  | float op base same =>
    rw [same] at byte accepted noncontrol
    exact reader_float_checked_prefix_wasm2 p ops law initial before after out ctx contextSource invariant C contextLocals
      monomorphic sourceBound bodyBound op base held exits byte accepted
  | sign op extension same =>
    rw [same] at byte accepted noncontrol
    exact reader_sign_checked_prefix_wasm2 p ops law initial before after out ctx contextSource invariant
      monomorphic sourceBound bodyBound op extension held exits byte accepted
  | load op same =>
    rw [same] at byte accepted noncontrol
    exact reader_memory_load_checked_prefix_wasm2 p ops law initial before after out ctx contextSource invariant C contextLocals
      matched.mems monomorphic sourceBound bodyBound op held exits byte accepted
  | store op same =>
    rw [same] at byte accepted noncontrol
    exact reader_memory_store_checked_prefix_wasm2 p ops law initial before after out ctx contextSource invariant C contextLocals
      matched.mems monomorphic sourceBound bodyBound op held exits byte accepted
  | typedSelect same =>
    rw [same] at byte accepted noncontrol
    exact reader_typed_select_checked_prefix_wasm2 p ops law initial before after out ctx invariant C contextLocals
      monomorphic sourceBound bodyBound held exits byte accepted
  | stateful member =>
    obtain ⟨op,a,b,arguments,callback,post⟩ := reader_stateful_base_wasm2 p
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx opcode member byte accepted
    rw [stateful_callback_lower ops before out.core op a b arguments] at callback
    exact post.instruction_prefix ops law initial before after C invariant monomorphic matched contextLocals
      a b arguments callback sourceBound bodyBound held exits
  | misc same =>
    rw [same] at byte accepted noncontrol
    obtain ⟨sub,next,decoded,choice⟩ := reader_misc_accepted
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index before after accepted
    rcases choice with ⟨op,extension,number⟩ | bulk
    · exact reader_saturating_checked_prefix_wasm2 p ops law initial before after out ctx contextSource invariant C contextLocals
        monomorphic sourceBound bodyBound op extension sub next number decoded held exits byte accepted
    · obtain ⟨op,a,b,arguments,callback,post⟩ := reader_stateful_bulk_wasm2 p
        (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx sub next bulk byte decoded accepted
      rw [stateful_callback_lower ops before out.core op a b arguments] at callback
      exact post.instruction_prefix ops law initial before after C invariant monomorphic matched contextLocals
        a b arguments callback sourceBound bodyBound held exits
  | simd same =>
    rw [same] at byte accepted noncontrol
    obtain ⟨event⟩ := reader_simd_event_wasm2 p ops before after out ctx C matched.mems byte accepted
    exact event.instruction_prefix law contextLocals invariant monomorphic sourceBound bodyBound held exits
  | control kind same =>
    rw [same] at byte accepted noncontrol
    cases kind <;> simp [ControlReaderKind.opcode,global_simps] at noncontrol
  | table same =>
    rw [same] at byte accepted noncontrol
    simp at noncontrol
  | reserved rejected =>
    exact False.elim (rejected.rejects (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st out data env ctx index opcode before after accepted)

end Itasca.Runtime.Compiler

end

/-! ## CheckedPrefixWasm2 -/

section

/-!
Every accepted Wasm 2 reader step preserves both concrete checking invariants from the retained source boundary. This covers the complete profile and does not assume an accepted future callback trace or final certificate.

Main declarations: `IndexedTableReaderCompilerPointWasm2.checked_prefix`. A direct consumer is `Compiler.Body.Reader.Checking.SourceCheckedStepsWasm2`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca


/-- Every accepted Wasm 2 reader step preserves both concrete checking
invariants from the retained source boundary. This covers the complete profile
and does not assume an accepted future callback trace or final certificate. -/
theorem IndexedTableReaderCompilerPointWasm2.checked_prefix {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {locals data env ctx index ft st} (C : context)
    (point : IndexedTableReaderCompilerPointWasm2 (fun tables => ExecutableEmission tables C) initial before
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft st)
    (initialLayout : LocalLayout initial) (initialLocals : compilerLocals initial = locals)
    (initialCapacity : initial.function.local_slots.val ≤ initial.function.slot_count.val)
    (localsMatch : initial.function.locals = ctx.locals) (metadata : FunctionParameterSlots initial env)
    (matched : EnvTranslation.Matches env ⟨ctx.locals,ft.results⟩ C) (contextLocals : C.LOCALS = locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyExtent : initial.function.body_end.val = initial.function.body_start.val+data.length)
    (bodyBound : initial.function.body_start.val+data.length ≤ Usize.max)
    (maps : ControlMapPublication before) (fixups : FixupBudget before.frames.val before.function.code.val.length)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (next : Usize) (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (opcode : U8) (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index opcode before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have sourceBound := state.boundary.source_bound
  have beforeBound := state.compiled.metadata.body_bound bodyBound
  obtain ⟨sameSignatures,sameFunctions,_,_,sameLocals,_,_,sameStart,sameEnd,_⟩ := state.compiled.metadata.fields
  have beforeLocals : before.function.locals = ctx.locals := sameLocals.trans localsMatch
  have beforeMetadata : FunctionParameterSlots before env := by
    simpa only [FunctionParameterSlots,sameFunctions] using metadata
  have beforeSignatures : SignatureSequence before.signatures.val env.types.val := by
    simpa only [sameSignatures] using signatures
  have beforeExtent : before.function.body_end.val = before.function.body_start.val+data.length := by
    rw [sameEnd,sameStart]
    exact bodyExtent
  by_cases table : opcode = 14#u8
  · rw [table,Wasm2.CallbackTrace.dispatch_br_table] at accepted
    exact reader_table_open_instructions_wasm2 p ops law initial before after out state.compiled state.sources state.fronts
      state.reach.current sourceBound beforeBound point.tables fixups held exits accepted
  by_cases noncontrol : opcode.val ∉ [2,3,4,5,11,12,13,14,15,16,17]
  · exact reader_noncontrol_checked_prefix_wasm2 p ops law initial before after out ctx rfl C state.compiled beforeLocals matched
      contextLocals state.reach.current sourceBound beforeBound opcode noncontrol held exits
      (by simpa only [p,ReaderBoundaryWasm2.pending] using byte) accepted
  · have member : opcode.val ∈ [2,3,4,5,11,12,13,15,16,17] := by
      have noTable : opcode.val ≠ 14 := fun equal => table (UScalar.eq_of_val_eq equal)
      simp only [List.mem_cons,List.not_mem_nil,or_false] at noncontrol ⊢
      tauto
    obtain ⟨kind,same⟩ := ControlReaderKind.of_opcode_mem opcode member
    rw [same] at byte accepted
    exact state.control_checked_prefix ops law ctx rfl C matched contextLocals beforeMetadata beforeSignatures
      initialLayout initialLocals initialCapacity beforeExtent beforeBound maps fixups held exits next advance inbounds out kind byte accepted

end Itasca.Runtime.Compiler

end
