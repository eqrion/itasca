import Itasca.Runtime.Compiler.Local.Checking.ScopeInstructionPrefixes
import Itasca.Runtime.Compiler.Body.Reader.Scalar.ScalarEffects
import Itasca.Runtime.Compiler.Body.Reader.GlobalEmissions
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Memory.MemoryEmissions
import Itasca.Runtime.Compiler.Body.Reader.Replay.OrdinaryEffects
import Itasca.Runtime.Compiler.Body.Callbacks.CompilerPrefixStart
import Itasca.Runtime.Compiler.Local.Callbacks.MetadataPreservation
import Itasca.Runtime.Compiler.Local.Source.SourceTactics
import Itasca.Runtime.Compiler.Local.Relations.Operations.CoreBasicEmissions
import Itasca.Runtime.Compiler.Body.Reader.Replay.MetadataTypes
import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState
import Itasca.Runtime.Compiler.Local.Relations.Stacks.ConcretePops
import Itasca.Runtime.Compiler.Local.Control.CodeSegmentsAndPositions
import Itasca.Runtime.Compiler.Local.Relations.Prefix.SuspendedPrefix
import Itasca.Runtime.Compiler.Local.Relations.Prefix.PrefixZipper
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant
import Itasca.Runtime.Compiler.Body.Reader.Float.FloatConstantEmissions
import Itasca.Runtime.Compiler.Local.Relations.LoweringEffects
import Itasca.Runtime.Compiler.Body.Reader.StackValues
import Itasca.Runtime.Compiler.Local.Lowering.Integer.Lowering
import Itasca.Runtime.Compiler.Body.Control.StructuredPrefixes
import Itasca.Runtime.Compiler.Body.Reader.Publication.NonScopeCallbackPublication
import Itasca.Runtime.Compiler.Local.Coordinates.InstructionTargetEffects
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableScratchLiteral
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CallbackRetention
import Itasca.Runtime.Compiler.Body.Reader.Control.ControlInstructionPrefixes
import Itasca.Runtime.Compiler.Body.Reader.Control.ReachedControlAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Replay.SingleCallback
import Itasca.Body.Trace.BytesDispatch
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.RecordedAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Publication.ScalarCallbackPublication
import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedCapacity
import Itasca.Runtime.Compiler.Body.Relations.Checking.ExecutableInstructionPrefix
import Itasca.Runtime.Compiler.Local.Relations.Table.ControlTablePreservation
import Itasca.Runtime.Compiler.Local.Lowering.ScalarTablePreservation
import Itasca.Runtime.Compiler.Body.Reader.References.TypedSelectEmission
import Itasca.Runtime.Compiler.Body.Reader.Source.SourceOpcodeFamilies
import Itasca.Runtime.Compiler.Body.Reader.Simd.Dispatch
import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdInstructionPrefix

/-!
Proofs for Runtime / Compiler / Body / Reader / Checking.

This module collects OperationInstructionPrefix, CheckedPrefix.
Each section documents its contracts and consumers.
-/

/-! ## OperationInstructionPrefix -/

section

/-!
# Operation Instruction Prefix

Integer and floating-point operations retain checked emitted prefixes. Dormant and live reader cases share the same source-bound instruction relation.
-/

/-! ## CoreInstructionPrefix -/

section

/-!
Actual source-typed local get reading preserves every stored instruction check.

Main declarations: `reader_local_get_open_instructions` and `reader_memory_store_open_instructions`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual source-typed local get reading preserves every stored instruction check. -/
theorem reader_local_get_open_instructions {data env locals typeIndex st}
    (p : Body.Pending data env locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (localsMatch : before.function.locals = locals)
    (types : List wasm_types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translation.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 32#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex code.OP_LOCAL_GET before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,index,ty,values,found,post,instruction,lowered,emission⟩ :=
    reader_emit_local_get p ops law before after out ctx contextLocals localsMatch types concrete layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_local_get_effects ops law before after st.core out.core data env ctx
    (base_step _ (by decide) (by decide) rfl (by simp only [global_simps]; decide) (by simpa only [global_simps] using accepted))).tables
  exact ⟨lowered.1.linear_instruction_prefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed local set reading preserves every stored instruction check. -/
theorem reader_local_set_open_instructions {data env locals typeIndex st}
    (p : Body.Pending data env locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (localsMatch : before.function.locals = locals)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Body.Stack.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 33#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex code.OP_LOCAL_SET before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,index,ty,values,front,found,input,post,instruction,lowered,emission⟩ :=
    reader_emit_local_set p ops law before after out ctx contextLocals localsMatch known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_local_set_effects ops law before after st.core out.core data env ctx
    (base_step _ (by decide) (by decide) rfl (by simp only [global_simps]; decide) (by simpa only [global_simps] using accepted))).tables
  rw [input] at layout
  exact ⟨lowered.1.linear_instruction_prefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed local tee reading preserves every stored instruction check. -/
theorem reader_local_tee_open_instructions {data env locals typeIndex st}
    (p : Body.Pending data env locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (localsMatch : before.function.locals = locals)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Body.Stack.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 34#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex code.OP_LOCAL_TEE before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,index,ty,values,front,found,input,post,instruction,lowered,emission⟩ :=
    reader_emit_local_tee p ops law before after out ctx contextLocals localsMatch known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_local_tee_effects ops law before after st.core out.core data env ctx
    (base_step _ (by decide) (by decide) rfl (by simp only [global_simps]; decide) (by simpa only [global_simps] using accepted))).tables
  rw [input] at layout
  exact ⟨lowered.1.linear_instruction_prefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed global get reading preserves every stored instruction check. -/
theorem reader_global_get_open_instructions {data env locals typeIndex st}
    (p : Body.Pending data env locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (C : context) (localsMatch : compilerLocals before = C.LOCALS)
    (globalsMatch : C.GLOBALS = env.global_types.val.map Translation.globalType)
    (types : List wasm_types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translation.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 35#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex code.OP_GLOBAL_GET before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,index,ty,values,found,post,instruction,lowered,emission⟩ :=
    reader_emit_global_get p ops law before after out ctx contextLocals C localsMatch globalsMatch types concrete layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_global_get_effects ops law before after st.core out.core data env ctx
    (base_step _ (by decide) (by decide) rfl (by simp only [global_simps]; decide) (by simpa only [global_simps] using accepted))).tables
  exact ⟨lowered.1.float_core_instruction_prefix layout reachable localsMatch.symm emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed global set reading preserves every stored instruction check. -/
theorem reader_global_set_open_instructions {data env locals typeIndex st}
    (p : Body.Pending data env locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (C : context) (localsMatch : compilerLocals before = C.LOCALS)
    (globalsMatch : C.GLOBALS = env.global_types.val.map Translation.globalType)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Body.Stack.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 36#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex code.OP_GLOBAL_SET before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,index,ty,values,front,found,mutable,input,post,instruction,lowered,emission⟩ :=
    reader_emit_global_set p ops law before after out ctx contextLocals C localsMatch globalsMatch known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_global_set_effects ops law before after st.core out.core data env ctx
    (base_step _ (by decide) (by decide) rfl (by simp only [global_simps]; decide) (by simpa only [global_simps] using accepted))).tables
  rw [input] at layout
  exact ⟨lowered.1.float_core_instruction_prefix layout reachable localsMatch.symm emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed select reading preserves every stored instruction check. -/
theorem reader_select_open_instructions {data env locals typeIndex st}
    (p : Body.Pending data env locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (C : context) (localsMatch : compilerLocals before = C.LOCALS)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Body.Stack.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 27#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex code.OP_SELECT before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,ty,front,values,input,post,instruction,lowered,emission⟩ :=
    reader_emit_select p ops law before after out ctx contextLocals C localsMatch known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_select_effects ops law before after st.core out.core data env ctx
    (base_step _ (by decide) (by decide) rfl (by simp only [global_simps]; decide) (by simpa only [global_simps] using accepted))).tables
  rw [input] at layout
  exact ⟨lowered.1.float_core_instruction_prefix layout reachable localsMatch.symm emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed memory load reading preserves every stored instruction check. -/
theorem reader_memory_load_open_instructions {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : SourceMachine.Memory.Load) (C : context)
    (contextLocalsCode : C.LOCALS = compilerLocals before)
    (contextMemories : C.MEMS = env.mem_types.val.map Translation.Environment.memType)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Body.Stack.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryLoadOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (memoryLoadOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,arg,front,values,input,post,instruction,lowered,emission⟩ :=
    reader_emit_memory_load p ops law before after out ctx contextLocals op C contextLocalsCode contextMemories known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_memory_load_effects ops law before after _ out data env ctx _ op accepted).tables
  rw [input] at layout
  exact ⟨lowered.1.float_core_instruction_prefix layout reachable contextLocalsCode emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed memory store reading preserves every stored instruction check. -/
theorem reader_memory_store_open_instructions {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : SourceMachine.Memory.Store) (C : context)
    (contextLocalsCode : C.LOCALS = compilerLocals before)
    (contextMemories : C.MEMS = env.mem_types.val.map Translation.Environment.memType)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Body.Stack.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryStoreOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (memoryStoreOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,arg,front,values,input,post,instruction,lowered,emission⟩ :=
    reader_emit_memory_store p ops law before after out ctx contextLocals op C contextLocalsCode contextMemories known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_memory_store_effects ops law before after _ out data env ctx _ op accepted).tables
  rw [input] at layout
  exact ⟨lowered.1.float_core_instruction_prefix layout reachable contextLocalsCode emission tables held stable.frames,stable.exit_slots exits⟩

end Itasca.Compiler

end

/-! ## OperationInstructionPrefix -/

section

/-!
Checked instruction prefixes for integer, float and memory reader operations. Live emission and dormant-source cases establish the common reader checking result.
-/

/-! ## Reader Dead Operation Instruction Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual unreachable numeric reading preserves both maintained checks. -/
theorem reader_dead_numeric_checked_prefix {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (dead : before.reachable = false)
    (op : SourceMachine.Numeric.Instruction) (standard : (integerOpcode op).val < 192)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨operation, hook, meaning, handler, instruction, inputs, output,
    hookEq, ordinary, baseOpcode, sign, misc⟩ := integer_reader_facts ops before out.core op standard
  obtain ⟨capacity, run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index _ before after ordinary baseOpcode sign misc contextLocals accepted
  obtain ⟨callback, read, _, _, values, effect, post⟩ := reader_numeric p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ operation hook
    capacity byte meaning handler run
  rw [hookEq] at callback
  exact compiler_dead_op_checked_prefix ops law before after out.core (integerOpcode op) 0#u32 0#u32 0#u128 dead held exits callback

/-- Actual unreachable float reading preserves both maintained checks. -/
theorem reader_dead_float_checked_prefix {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (dead : before.reachable = false)
    (op : SourceMachine.Float.Instruction) (standard : (floatOpcode op).val < 256)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (floatOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (floatOpcode op)) before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨operation, hook, meaning, handler, instruction, inputs, output,
    hookEq, ordinary, baseOpcode, sign, misc⟩ := float_reader_facts ops before out.core op standard
  obtain ⟨capacity, run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index _ before after ordinary baseOpcode sign misc contextLocals accepted
  obtain ⟨callback, read, _, _, values, effect, post⟩ := reader_numeric p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ operation hook
    capacity byte meaning handler run
  rw [hookEq] at callback
  exact compiler_dead_op_checked_prefix ops law before after out.core (floatOpcode op) 0#u32 0#u32 0#u128 dead held exits callback

/-- Actual unreachable memory load reading preserves both maintained checks. -/
theorem reader_dead_memory_load_checked_prefix {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (dead : before.reachable = false) (op : SourceMachine.Memory.Load)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryLoadOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (memoryLoadOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨meaning,_,_,_,_,ordinary,base,sign,misc⟩ := memory_load_reader_facts ops before out.core op ⟨0#u32,0#u32⟩
  obtain ⟨capacity,run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals,p.ft.results⟩ index _ before after ordinary base sign misc contextLocals accepted
  obtain ⟨arg,values,callback,read,post⟩ := reader_memory p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ (memoryLoadMeaning op)
    capacity byte meaning run
  obtain ⟨_,_,_,source,callbackEq,_⟩ := memory_load_reader_facts ops before out.core op arg
  rw [callbackEq] at callback
  rw [source] at post
  exact compiler_dead_op_checked_prefix ops law before after out.core (memoryLoadOpcode op) arg.offset arg.align 0#u128 dead held exits callback

/-- Actual unreachable memory store reading preserves both maintained checks. -/
theorem reader_dead_memory_store_checked_prefix {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (dead : before.reachable = false) (op : SourceMachine.Memory.Store)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryStoreOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (memoryStoreOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨meaning,_,_,_,_,ordinary,base,sign,misc⟩ := memory_store_reader_facts ops before out.core op ⟨0#u32,0#u32⟩
  obtain ⟨capacity,run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals,p.ft.results⟩ index _ before after ordinary base sign misc contextLocals accepted
  obtain ⟨arg,values,callback,read,post⟩ := reader_memory p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ (memoryStoreMeaning op)
    capacity byte meaning run
  obtain ⟨_,_,_,source,callbackEq,_⟩ := memory_store_reader_facts ops before out.core op arg
  rw [callbackEq] at callback
  rw [source] at post
  exact compiler_dead_op_checked_prefix ops law before after out.core (memoryStoreOpcode op) arg.offset arg.align 0#u128 dead held exits callback

/-- Actual unreachable saturating reading preserves both maintained checks. -/
theorem reader_dead_saturating_checked_prefix {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (dead : before.reachable = false)
    (op : SourceMachine.Float.Instruction) (extension : 256 ≤ (floatOpcode op).val)
    (subopcode : U32) (next : Usize)
    (subopcodeEq : subopcode.val = (floatOpcode op).val - 256)
    (decoded : Binary.Leb128.Decoded data st.core.pos subopcode next)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 0xfc#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (0xfc#u8) before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨operation,instruction,inputs,output,callback,_,_,_,_,values,effect,post⟩ :=
    reader_float_saturating p ops before after out ctx op extension subopcode next subopcodeEq decoded byte accepted
  exact compiler_dead_op_checked_prefix ops law before after out.core (floatOpcode op) 0#u32 0#u32 0#u128 dead held exits callback

/-- Sign-extension reading in dead code only observes the returned stack. -/
theorem reader_dead_sign_checked_prefix {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (dead : before.reachable = false) (op : SourceMachine.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨operation,instruction,inputs,output,callback,_⟩ := reader_integer_sign p ops before after out ctx op extension byte accepted
  exact compiler_dead_op_checked_prefix ops law before after out.core (integerOpcode op) 0#u32 0#u32 0#u128 dead held exits callback

end Itasca.Compiler

end

/-! ## Reader Numeric Instruction Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual typed integer reader progress preserves all stored instruction checks. -/
theorem reader_numeric_open_instructions {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : SourceMachine.Numeric.Instruction) (baseOpcode : (integerOpcode op).val < 192)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Body.Stack.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,front,values,input,post,instruction,lowered,emission⟩ :=
    reader_emit_numeric p ops law before after out ctx contextLocals op baseOpcode known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_numeric_effects p ops law before after out ctx op byte accepted).tables
  rw [input] at layout
  exact ⟨lowered.1.linear_instruction_prefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual typed integer reader progress preserves all stored instruction checks. -/
theorem reader_sign_open_instructions {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : SourceMachine.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Body.Stack.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,front,values,input,post,instruction,lowered,emission⟩ :=
    reader_emit_sign p ops law before after out ctx contextLocals op extension known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_numeric_effects p ops law before after out ctx op byte accepted).tables
  rw [input] at layout
  exact ⟨lowered.1.linear_instruction_prefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

end Itasca.Compiler

end

/-! ## Reader Float Instruction Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual typed floating-point reader progress preserves all stored instruction checks. -/
theorem reader_float_open_instructions {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : SourceMachine.Float.Instruction) (C : context)
    (contextLocalsCode : C.LOCALS = compilerLocals before) (baseOpcode : (floatOpcode op).val < 256)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Body.Stack.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (floatOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (floatOpcode op)) before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,front,values,input,post,instruction,lowered,emission⟩ :=
    reader_emit_float p ops law before after out ctx contextLocals op C contextLocalsCode baseOpcode known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_float_base_effects ops law before after _ out data env ctx _ op baseOpcode accepted).tables
  rw [input] at layout
  exact ⟨lowered.1.float_core_instruction_prefix layout reachable contextLocalsCode emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual typed floating-point reader progress preserves all stored instruction checks. -/
theorem reader_saturating_open_instructions {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : SourceMachine.Float.Instruction) (C : context)
    (contextLocalsCode : C.LOCALS = compilerLocals before) (extension : 256 ≤ (floatOpcode op).val)
    (subopcode : U32) (next : Usize)
    (subopcodeEq : subopcode.val = (floatOpcode op).val - 256)
    (decoded : Binary.Leb128.Decoded data st.core.pos subopcode next)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Body.Stack.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 0xfc#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (0xfc#u8) before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,front,values,input,post,instruction,lowered,emission⟩ :=
    reader_emit_saturating p ops law before after out ctx contextLocals op C contextLocalsCode extension subopcode next subopcodeEq decoded known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_saturating_effects p ops law before after out ctx op extension subopcode next subopcodeEq decoded byte accepted).tables
  rw [input] at layout
  exact ⟨lowered.1.float_core_instruction_prefix layout reachable contextLocalsCode emission tables held stable.frames,stable.exit_slots exits⟩

end Itasca.Compiler

end

/-! ## Reader Operation Instruction Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Source-prefix geometry supplies live operation checks; dead reading only observes. -/
theorem reader_numeric_checked_prefix {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (contextSource : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (op : SourceMachine.Numeric.Instruction) (baseOpcode : (integerOpcode op).val < 192)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  by_cases live : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live live
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    exact reader_numeric_open_instructions p ops law before after out ctx contextSource op baseOpcode (invariant.known live) (monomorphic live) retained.layout live
      codeFits sourceFits coordinateFits held exits byte accepted
  · exact reader_dead_numeric_checked_prefix p ops law before after out ctx contextSource (Bool.eq_false_iff.mpr live) op baseOpcode held exits byte accepted

/-- Source-prefix geometry supplies live operation checks; dead reading only observes. -/
theorem reader_float_checked_prefix {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (contextSource : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (C : context) (contextLocals : C.LOCALS = locals)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (op : SourceMachine.Float.Instruction) (baseOpcode : (floatOpcode op).val < 256)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (floatOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (floatOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  by_cases live : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live live
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    exact reader_float_open_instructions p ops law before after out ctx contextSource op C (contextLocals.trans retained.localsEq.symm) baseOpcode (invariant.known live) (monomorphic live) retained.layout live
      codeFits sourceFits coordinateFits held exits byte accepted
  · exact reader_dead_float_checked_prefix p ops law before after out ctx contextSource (Bool.eq_false_iff.mpr live) op baseOpcode held exits byte accepted

/-- Source-prefix geometry supplies live operation checks; dead reading only observes. -/
theorem reader_memory_load_checked_prefix {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (contextSource : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (C : context) (contextLocals : C.LOCALS = locals)
    (contextMemories : C.MEMS = env.mem_types.val.map Translation.Environment.memType)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (op : SourceMachine.Memory.Load)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryLoadOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (memoryLoadOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  by_cases live : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live live
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    exact reader_memory_load_open_instructions p ops law before after out ctx contextSource op C (contextLocals.trans retained.localsEq.symm) contextMemories (invariant.known live) (monomorphic live) retained.layout live
      codeFits sourceFits coordinateFits held exits byte accepted
  · exact reader_dead_memory_load_checked_prefix p ops law before after out ctx contextSource (Bool.eq_false_iff.mpr live) op held exits byte accepted

/-- Source-prefix geometry supplies live operation checks; dead reading only observes. -/
theorem reader_memory_store_checked_prefix {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (contextSource : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (C : context) (contextLocals : C.LOCALS = locals)
    (contextMemories : C.MEMS = env.mem_types.val.map Translation.Environment.memType)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (op : SourceMachine.Memory.Store)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryStoreOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (memoryStoreOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  by_cases live : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live live
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    exact reader_memory_store_open_instructions p ops law before after out ctx contextSource op C (contextLocals.trans retained.localsEq.symm) contextMemories (invariant.known live) (monomorphic live) retained.layout live
      codeFits sourceFits coordinateFits held exits byte accepted
  · exact reader_dead_memory_store_checked_prefix p ops law before after out ctx contextSource (Bool.eq_false_iff.mpr live) op held exits byte accepted

/-- Source-prefix geometry supplies live operation checks; dead reading only observes. -/
theorem reader_sign_checked_prefix {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (contextSource : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (op : SourceMachine.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  by_cases live : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live live
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    exact reader_sign_open_instructions p ops law before after out ctx contextSource op extension (invariant.known live) (monomorphic live) retained.layout live
      codeFits sourceFits coordinateFits held exits byte accepted
  · exact reader_dead_sign_checked_prefix p ops law before after out ctx (Bool.eq_false_iff.mpr live) op extension held exits byte accepted

/-- Source-prefix geometry supplies live operation checks; dead reading only observes. -/
theorem reader_saturating_checked_prefix {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (contextSource : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (C : context) (contextLocals : C.LOCALS = locals)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (op : SourceMachine.Float.Instruction) (extension : 256 ≤ (floatOpcode op).val) (subopcode : U32) (next : Usize)
    (subopcodeEq : subopcode.val = (floatOpcode op).val-256)
    (decoded : Binary.Leb128.Decoded data st.core.pos subopcode next)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 0xfc#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (0xfc#u8) before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  by_cases live : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live live
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    exact reader_saturating_open_instructions p ops law before after out ctx contextSource op C (contextLocals.trans retained.localsEq.symm) extension subopcode next subopcodeEq decoded (invariant.known live) (monomorphic live) retained.layout live
      codeFits sourceFits coordinateFits held exits byte accepted
  · exact reader_dead_saturating_checked_prefix p ops law before after out ctx contextSource (Bool.eq_false_iff.mpr live) op extension subopcode next subopcodeEq decoded held exits byte accepted

end Itasca.Compiler

end

end

end

/-! ## CheckedPrefix -/

section

/-!
Proofs for Runtime / Compiler / Body / Reader / Checking.

This module collects JumpTargets, CheckedPrefix.
Each section documents its contracts and consumers.
-/

/-! ## JumpTargets -/

section

/-!
Published jump-target bounds across ordinary and scope reader steps. The final reader theorem assembles the operation-specific target bounds.
-/

/-! ## Non Scope Target Bounds -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- Every non-scope-boundary event retains valid jump-table targets. Tables
append only actual branch-stub positions; all other callbacks retain the table. -/
theorem compiler_non_scope_hook_target_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) {action : Action} (supported : NonScopePublicationAction action)
    (held : JumpTableBounds before)
    (called : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before (.op state action) =
      .ok (.Ok (),after)) : JumpTableBounds after := by
  cases supported with
  | scalar supported =>
    obtain ⟨opcode,a,b,bits,member,dispatch⟩ := scalar_hook_publication_dispatch ops before state supported
    rw [dispatch] at called
    exact compiler_scalar_target_bounds ops law before after state opcode a b bits member held called
  | numeric hook =>
    rcases numeric_hook_publication_dispatch ops before state hook with ⟨op,dispatch⟩ | ⟨op,dispatch⟩
    · rw [dispatch] at called
      exact compiler_numeric_target_bounds ops law before after state op held called
    · rw [dispatch] at called
      exact compiler_float_target_bounds ops law before after state op held called
  | extendedNumeric hook =>
    rcases extended_numeric_hook_publication_dispatch ops before state hook with ⟨op,dispatch⟩ | ⟨op,dispatch⟩
    · rw [dispatch] at called
      exact compiler_numeric_target_bounds ops law before after state op held called
    · rw [dispatch] at called
      exact compiler_float_target_bounds ops law before after state op held called
  | memory hook arg =>
    have range : 40 ≤ hook.opcode.val ∧ hook.opcode.val ≤ 62 := by cases hook <;> decide
    have visited := (MemoryHook.dispatch (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before state hook arg).trans called
    rcases source_memory_byte_partition hook.opcode range.1 range.2 with ⟨op,byte⟩ | ⟨op,byte⟩
    · have dispatch := (memory_load_reader_facts ops before state op arg).2.2.2.2.1
      rw [← byte,dispatch] at visited
      exact compiler_core_target_bounds ops law before after state (.load op arg.offset arg.align) held visited
    · have dispatch := (memory_store_reader_facts ops before state op arg).2.2.2.2.1
      rw [← byte,dispatch] at visited
      exact compiler_core_target_bounds ops law before after state (.store op arg.offset arg.align) held visited
  | simd supported =>
    obtain ⟨opcode,a,b,bits,lower,upper,dispatch⟩ := simd_hook_publication_dispatch ops before state supported
    rw [dispatch] at called
    exact compiler_simd_target_bounds ops law before after state opcode a b bits lower upper held called
  | unreachable =>
    exact held.retained (after := after)
      (congrArg CompilerTables.jumpTables (compiler_unreachable_tables ops law before after state called))
      (compiler_unreachable_code_mono ops law before after state called)
  | return_ =>
    exact held.retained (after := after)
      (congrArg CompilerTables.jumpTables (compiler_return_tables ops law before after state called))
      (compiler_return_code_mono ops law before after state called)
  | br depth types =>
    exact held.retained (after := after)
      (congrArg CompilerTables.jumpTables (compiler_br_tables ops law before after state depth types called))
      (compiler_br_code_mono ops law before after state depth types called)
  | br_if depth types =>
    exact held.retained (after := after)
      (congrArg CompilerTables.jumpTables (compiler_br_if_tables ops law before after state depth types called))
      (compiler_br_if_code_mono ops law before after state depth types called)
  | label depth => exact compiler_table_label_target_bounds ops law before after state depth held called
  | table fallback types => exact compiler_br_table_target_bounds ops law before after state fallback types held called
  | else_ bt =>
    exact held.retained (after := after)
      (congrArg CompilerTables.jumpTables (compiler_else_tables ops law before after state bt called))
      (compiler_else_code_mono ops law before after state bt called)

end Itasca.Compiler

end

/-! ## Reader Target Bounds -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- Actual Wasm 2 openings retain targets independently of the selected signature. -/
theorem reader_enter_target_bounds {data env localTypes index st}
    (p : Body.Pending data env localTypes index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (held : JumpTableBounds before) (form : Body.Frames.Form) (initial : form.Initial)
    (byte : data.val[p.start.val]'p.inbounds = form.opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index form.opcode before = .ok (.Ok (),out,after)) : JumpTableBounds after := by
  obtain ⟨bt,ins,outs,remaining,base,callback,_,post⟩ := reader_enter p form initial
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have called : runtime.compiler.control.FunctionCompiler.enter ops before out.core form.kind bt = .ok (.Ok (),after) := by
    rcases initial with rfl | rfl | rfl <;> exact callback
  exact compiler_enter_target_bounds ops law before after out.core form.kind bt held called

/-- Actual Wasm 2 END retains target bounds while patching instructions. -/
theorem reader_end_target_bounds {data env localTypes index st}
    (p : Body.Pending data env localTypes index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (held : JumpTableBounds before) (byte : data.val[p.start.val]'p.inbounds = 11#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx index 11#u8 before = .ok (.Ok (),out,after)) : JumpTableBounds after := by
  have callback := (reader_end p (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    before after out ctx byte accepted).1
  exact compiler_end_target_bounds ops law before after out.core p.current.ctrl.kind p.current.bt held callback

/-- Wasm 2 selector and label collection retain all prior targets before dispatch. -/
theorem reader_table_target_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.BodyState) (data : Slice U8) (env : metadata.Env) (held : JumpTableBounds before)
    (accepted : code.branch_table_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env before = .ok (.Ok (),final,after)) : JumpTableBounds after := by
  obtain ⟨count,first,selector,popped,depths,fallback,types,last,readState,budget,buffer,_,_,_,_,_,_,_,callback⟩ :=
    compiler_read_br_table ops law before after st final data env accepted
  exact compiler_br_table_target_bounds ops law {before with budget,table_depths := buffer} after final.core fallback
    types (by simpa only [JumpTableBounds] using held) callback

end Itasca.Compiler

end

/-! ## Reader Jump Targets -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace Itasca.Body

/-- Every accepted complete Wasm 2 reader step retains bounded jump
targets, including SIMD, dead bodies, branches, references and streamed tables. -/
theorem reader_jump_targets {data env localTypes index st}
    (p : Body.Pending data env localTypes index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (held : JumpTableBounds before)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (data.val[p.start.val]'p.inbounds) before = .ok (.Ok (),out,after)) : JumpTableBounds after := by
  let opcode := data.val[p.start.val]'p.inbounds
  by_cases h2 : opcode = 2#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index 2#u8 before = .ok (.Ok (),out,after) := by simpa only [← h2] using accepted
    exact reader_enter_target_bounds p ops law before after out ctx held .block (.inl rfl) h2 call
  by_cases h3 : opcode = 3#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index 3#u8 before = .ok (.Ok (),out,after) := by simpa only [← h3] using accepted
    exact reader_enter_target_bounds p ops law before after out ctx held .loop (.inr (.inl rfl)) h3 call
  by_cases h4 : opcode = 4#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index 4#u8 before = .ok (.Ok (),out,after) := by simpa only [← h4] using accepted
    exact reader_enter_target_bounds p ops law before after out ctx held .then_ (.inr (.inr rfl)) h4 call
  by_cases h11 : opcode = 11#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index 11#u8 before = .ok (.Ok (),out,after) := by simpa only [← h11] using accepted
    exact reader_end_target_bounds p ops law before after out ctx held h11 call
  by_cases h14 : opcode = 14#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index 14#u8 before = .ok (.Ok (),out,after) := by simpa only [← h14] using accepted
    rw [CallbackTrace.dispatch_br_table] at call
    exact reader_table_target_bounds ops law before after st out data env held call
  have blocked : opcode ≠ code.OP_BLOCK ∧ opcode ≠ code.OP_LOOP ∧ opcode ≠ code.OP_IF ∧
      opcode ≠ code.OP_END ∧ opcode ≠ code.OP_BR_TABLE := by
    simp only [global_simps]
    tauto
  obtain ⟨action,ordinary,range,callback⟩ := reader_single_body_callback
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index opcode before after blocked accepted
  exact compiler_non_scope_hook_target_bounds ops law before after out.core (.of_range action range ordinary) held callback

end Itasca.Compiler

end

end

/-! ## CheckedPrefix -/

section

/-!
# Checked Prefix

Scalar, stateful and typed-select prefixes satisfy the stored instruction checks. Their noncontrol cases combine into the checked reader-prefix invariant.
-/

/-! ## ScalarInstructionPrefix -/

section

/-!
Checked prefixes for constants, nop/drop and dormant scalar reader cases, composed into complete scalar instruction checking.
-/

/-! ## Reader Constant Instruction Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual typed literal reading checks its emitted word and retains earlier checks. -/
theorem reader_const32_open_instructions {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List wasm_types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translation.valueType))
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
    reader_emit_const32 p ops law before after out ctx contextLocals types concrete layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_i32_const_effects ops law before after st.core out.core data env ctx
    (base_step _ (by decide) (by decide) rfl (by simp only [global_simps]; decide) (by simpa only [global_simps] using accepted))).tables
  exact ⟨lowered.1.linear_instruction_prefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual typed literal reading checks its emitted word and retains earlier checks. -/
theorem reader_const64_open_instructions {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List wasm_types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translation.valueType))
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
    reader_emit_const64 p ops law before after out ctx contextLocals types concrete layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_i64_const_effects ops law before after st.core out.core data env ctx
    (base_step _ (by decide) (by decide) rfl (by simp only [global_simps]; decide) (by simpa only [global_simps] using accepted))).tables
  exact ⟨lowered.1.linear_instruction_prefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual typed literal reading checks its emitted word and retains earlier checks. -/
theorem reader_float32_open_instructions {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A)
    (C : context) (localTypes : C.LOCALS = compilerLocals before) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List wasm_types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translation.valueType))
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
    reader_emit_float32 p ops law before after C localTypes out ctx contextLocals types concrete layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_f32_const_effects ops law before after st.core out.core data env ctx
    (base_step _ (by decide) (by decide) rfl (by simp only [global_simps]; decide) (by simpa only [global_simps] using accepted))).tables
  exact ⟨lowered.1.float_core_instruction_prefix layout reachable localTypes emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual typed literal reading checks its emitted word and retains earlier checks. -/
theorem reader_float64_open_instructions {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A)
    (C : context) (localTypes : C.LOCALS = compilerLocals before) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (types : List wasm_types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translation.valueType))
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
    reader_emit_float64 p ops law before after C localTypes out ctx contextLocals types concrete layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_f64_const_effects ops law before after st.core out.core data env ctx
    (base_step _ (by decide) (by decide) rfl (by simp only [global_simps]; decide) (by simpa only [global_simps] using accepted))).tables
  exact ⟨lowered.1.float_core_instruction_prefix layout reachable localTypes emission tables held stable.frames,stable.exit_slots exits⟩

end Itasca.Compiler

end

/-! ## Reader Dead Scalar Instruction Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

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
  obtain ⟨value,_,callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ accepted
  by_cases trap : kind = .unreachable
  · subst kind
    exact ⟨compiler_unreachable_open_instructions ops law before after out codeFits sourceFits coordinateFits held callback,
      (compiler_unreachable_ordinary_result ops law before after out (.Ok ()) callback).exit_slots exits⟩
  · have supported : ScalarPublicationAction (kind.action value) := by
      cases kind <;> first | contradiction | constructor
    obtain ⟨opcode,a,b,bits,_,dispatch⟩ := scalar_hook_publication_dispatch ops before out supported
    rw [dispatch] at callback
    exact compiler_dead_op_checked_prefix ops law before after out opcode a b bits dead held exits callback

end Itasca.Compiler

end

/-! ## Reader Noop Instruction Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- Actual nop reading preserves instruction and recorded exit-slot checks. -/
theorem reader_nop_open_instructions {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 1#u8 before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨_,run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 1#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_nop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ run
  cases value
  exact compiler_nop_drop_open_instructions ops law before after out.core false held exits callback

/-- Actual drop reading preserves instruction and recorded exit-slot checks. -/
theorem reader_drop_open_instructions {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 26#u8 before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨_,run⟩ := base_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 26#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_drop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ run
  exact compiler_nop_drop_open_instructions ops law before after out.core true held exits callback

end Itasca.Compiler

end

/-! ## Reader Scalar Instruction Prefix Body -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Every scalar reader kind preserves both instruction and recorded exit-slot
checks from its source-typed prefix, including all unreachable variants. -/
theorem reader_scalar_checked_prefix {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (contextSource : ctx.locals = sourceLocals) (C : context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (localsMatch : before.function.locals = sourceLocals)
    (contextLocals : C.LOCALS = locals)
    (globalsMatch : C.GLOBALS = env.global_types.val.map Translation.globalType)
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
    have literalLayout : CompilerLayout before (rawTypes.map Translation.valueType) := by
      simpa only [concrete,Body.Stack.stackTypes,List.map_map,Function.comp_def] using layout
    cases kind with
    | nop =>
      exact reader_nop_open_instructions ops law before after st out data env ctx index held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | unreachable =>
      exact reader_unreachable_open_instructions p ops law initial before after out ctx contextSource invariant held exits bodyBound (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | drop =>
      exact reader_drop_open_instructions ops law before after st out data env ctx index held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | select =>
      exact reader_select_open_instructions p ops law before after out ctx contextSource C localTypes.symm known (monomorphic live) layout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | local_get =>
      exact reader_local_get_open_instructions p ops law before after out ctx contextSource localsMatch rawTypes concrete literalLayout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | local_set =>
      exact reader_local_set_open_instructions p ops law before after out ctx contextSource localsMatch known (monomorphic live) layout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | local_tee =>
      exact reader_local_tee_open_instructions p ops law before after out ctx contextSource localsMatch known (monomorphic live) layout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | global_get =>
      exact reader_global_get_open_instructions p ops law before after out ctx contextSource C localTypes.symm globalsMatch rawTypes concrete literalLayout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | global_set =>
      exact reader_global_set_open_instructions p ops law before after out ctx contextSource C localTypes.symm globalsMatch known (monomorphic live) layout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | i32_const =>
      exact reader_const32_open_instructions p ops law before after out ctx contextSource rawTypes concrete literalLayout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | i64_const =>
      exact reader_const64_open_instructions p ops law before after out ctx contextSource rawTypes concrete literalLayout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | f32_const =>
      exact reader_float32_open_instructions p ops law before after C localTypes out ctx contextSource rawTypes concrete literalLayout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | f64_const =>
      exact reader_float64_open_instructions p ops law before after C localTypes out ctx contextSource rawTypes concrete literalLayout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
  · obtain ⟨_,raw⟩ := base_success
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index kind.opcode before after
      kind.ordinary kind.plain kind.sign kind.misc rfl accepted
    exact reader_dead_scalar_checked_prefix ops law before after st.core out.core data env ctx kind
      (Bool.eq_false_iff.mpr live) codeFits sourceFits coordinateFits held exits raw

end Itasca.Compiler

end

end

/-! ## StatefulInstructionPrefix -/

section

/-!
Source-typed stateful metadata readers check every newly emitted word and retain both pending instruction checks and the slots of recorded exits.

Main declarations: `StatefulReaderPost.instruction_prefix`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Source-typed stateful metadata readers check every newly emitted word and
retain both pending instruction checks and the slots of recorded exits. -/
theorem StatefulReaderPost.instruction_prefix {jumpTables : List U32} {data env sourceLocals index st}
    {p : Body.Pending data env sourceLocals index st} {out : code.OpIterState} {op : SourceMachine.Stateful.Instruction}
    (post : StatefulReaderPost p out op) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (C : context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (matched : Translation.Environment.Matches env ⟨sourceLocals,p.ft.results⟩ C)
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
    rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (reachable)] at callback
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

end Itasca.Compiler

end

/-! ## TypedSelectCheckedPrefix -/

section

/-!
Open-instruction and checked-prefix preservation for typed-select reader steps.
-/

/-! ## Reader Typed Select Instruction Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual typed select uses the source-selected width for its instruction check. -/
theorem reader_typed_select_open_instructions {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (C : context) (localsMatch : compilerLocals before = C.LOCALS)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Body.Stack.stackTypes st.core.vals.val))
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
    reader_emit_typed_select p ops law before after out ctx C localsMatch known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  obtain ⟨other,position,callback,_⟩ := reader_typed_select p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 28#u16 0#u32 0#u32 0#u128 = _ at callback
  have tables := compiler_core_tables ops law before after out.core (.select true) callback
  have growth := lowered.1.instruction_check_extends tables
  rw [input] at layout
  exact ⟨lowered.1.executable_instruction_prefix layout reachable localsMatch.symm
    (.typedSelect emission) (by intro depths fallback same; cases same) growth held stable.frames,
    exits.retained (congrArg alloc.vec.Vec.val stable.frames) stable.capacity⟩

end Itasca.Compiler

end

/-! ## Reader Typed Select Checked Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Typed select preserves both invariants for either source reachability bit;
only live source code emits the selected-width instruction. -/
theorem reader_typed_select_checked_prefix {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
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
    exact reader_typed_select_open_instructions p ops law before after out ctx C
      (retained.localsEq.trans contextLocals.symm) (invariant.known live) (monomorphic live) retained.layout live
      codeFits sourceFits coordinateFits held exits byte accepted
  · obtain ⟨ty,position,callback,_⟩ := reader_typed_select p
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
    change runtime.compiler.lower.FunctionCompiler.op ops before out.core 28#u16 0#u32 0#u32 0#u128 = _ at callback
    exact compiler_dead_op_checked_prefix ops law before after out.core 28#u16 0#u32 0#u32 0#u128
      (Bool.eq_false_iff.mpr live) held exits callback

end Itasca.Compiler

end

end

/-! ## NoncontrolCheckedPrefix -/

section

/-!
Source opcode coverage composes every noncontrol Wasm 2 reader family, including unreachable code, bulk operations, typed select, and all SIMD forms. The excluded control cases have separate source-frame adapters.

Main declarations: `reader_noncontrol_checked_prefix`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Source opcode coverage composes every noncontrol Wasm 2 reader family,
including unreachable code, bulk operations, typed select, and all SIMD forms.
The excluded control cases have separate source-frame adapters. -/
theorem reader_noncontrol_checked_prefix {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (contextSource : ctx.locals = sourceLocals) (C : context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (localsMatch : before.function.locals = sourceLocals)
    (matched : Translation.Environment.Matches env ⟨sourceLocals,p.ft.results⟩ C)
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
    exact reader_scalar_checked_prefix p ops law initial before after out ctx contextSource C invariant localsMatch
      contextLocals matched.globals monomorphic sourceBound bodyBound kind held exits byte accepted
  | integer op base same =>
    rw [same] at byte accepted noncontrol
    exact reader_numeric_checked_prefix p ops law initial before after out ctx contextSource invariant
      monomorphic sourceBound bodyBound op base held exits byte accepted
  | float op base same =>
    rw [same] at byte accepted noncontrol
    exact reader_float_checked_prefix p ops law initial before after out ctx contextSource invariant C contextLocals
      monomorphic sourceBound bodyBound op base held exits byte accepted
  | sign op extension same =>
    rw [same] at byte accepted noncontrol
    exact reader_sign_checked_prefix p ops law initial before after out ctx contextSource invariant
      monomorphic sourceBound bodyBound op extension held exits byte accepted
  | load op same =>
    rw [same] at byte accepted noncontrol
    exact reader_memory_load_checked_prefix p ops law initial before after out ctx contextSource invariant C contextLocals
      matched.mems monomorphic sourceBound bodyBound op held exits byte accepted
  | store op same =>
    rw [same] at byte accepted noncontrol
    exact reader_memory_store_checked_prefix p ops law initial before after out ctx contextSource invariant C contextLocals
      matched.mems monomorphic sourceBound bodyBound op held exits byte accepted
  | typedSelect same =>
    rw [same] at byte accepted noncontrol
    exact reader_typed_select_checked_prefix p ops law initial before after out ctx invariant C contextLocals
      monomorphic sourceBound bodyBound held exits byte accepted
  | stateful member =>
    obtain ⟨op,a,b,arguments,callback,post⟩ := reader_stateful_base p
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx opcode member byte accepted
    rw [stateful_callback_lower ops before out.core op a b arguments] at callback
    exact post.instruction_prefix ops law initial before after C invariant monomorphic matched contextLocals
      a b arguments callback sourceBound bodyBound held exits
  | misc same =>
    rw [same] at byte accepted noncontrol
    obtain ⟨sub,next,decoded,choice⟩ := reader_misc_accepted
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index before after accepted
    rcases choice with ⟨op,extension,number⟩ | bulk
    · exact reader_saturating_checked_prefix p ops law initial before after out ctx contextSource invariant C contextLocals
        monomorphic sourceBound bodyBound op extension sub next number decoded held exits byte accepted
    · obtain ⟨op,a,b,arguments,callback,post⟩ := reader_stateful_bulk p
        (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx sub next bulk byte decoded accepted
      rw [stateful_callback_lower ops before out.core op a b arguments] at callback
      exact post.instruction_prefix ops law initial before after C invariant monomorphic matched contextLocals
        a b arguments callback sourceBound bodyBound held exits
  | simd same =>
    rw [same] at byte accepted noncontrol
    obtain ⟨event⟩ := reader_simd_event p ops before after out ctx C matched.mems byte accepted
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

end Itasca.Compiler

end

/-! ## CheckedPrefix -/

section

/-!
Every accepted Wasm 2 reader step preserves both concrete checking invariants from the retained source boundary. This covers the complete instruction set and does not assume an accepted future callback trace or final certificate.

Main declarations: `IndexedTableReaderCompilerPoint.checked_prefix`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Every accepted Wasm 2 reader step preserves both concrete checking
invariants from the retained source boundary. This covers the complete instruction set
and does not assume an accepted future callback trace or final certificate. -/
theorem IndexedTableReaderCompilerPoint.checked_prefix {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {locals data env ctx index ft st} (C : context)
    (point : IndexedTableReaderCompilerPoint (fun tables => ExecutableEmission tables C) initial before
      (env.types.val.map Translation.Environment.funcType) (env.func_types.val.map Translation.Environment.funcType)
      (ft.results.val.map Translation.valueType) locals data env ctx.locals index ft st)
    (initialLayout : LocalLayout initial) (initialLocals : compilerLocals initial = locals)
    (initialCapacity : initial.function.local_slots.val ≤ initial.function.slot_count.val)
    (localsMatch : initial.function.locals = ctx.locals) (metadata : FunctionParameterSlots initial env)
    (matched : Translation.Environment.Matches env ⟨ctx.locals,ft.results⟩ C) (contextLocals : C.LOCALS = locals)
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
  · rw [table,Body.CallbackTrace.dispatch_br_table] at accepted
    exact reader_table_open_instructions p ops law initial before after out state.compiled state.sources state.fronts
      state.reach.current sourceBound beforeBound point.tables fixups held exits accepted
  by_cases noncontrol : opcode.val ∉ [2,3,4,5,11,12,13,14,15,16,17]
  · exact reader_noncontrol_checked_prefix p ops law initial before after out ctx rfl C state.compiled beforeLocals matched
      contextLocals state.reach.current sourceBound beforeBound opcode noncontrol held exits
      (by simpa only [p,ReaderBoundary.pending] using byte) accepted
  · have member : opcode.val ∈ [2,3,4,5,11,12,13,15,16,17] := by
      have noTable : opcode.val ≠ 14 := fun equal => table (UScalar.eq_of_val_eq equal)
      simp only [List.mem_cons,List.not_mem_nil,or_false] at noncontrol ⊢
      tauto
    obtain ⟨kind,same⟩ := ControlReaderKind.of_opcode_mem opcode member
    rw [same] at byte accepted
    exact state.control_checked_prefix ops law ctx rfl C matched contextLocals beforeMetadata beforeSignatures
      initialLayout initialLocals initialCapacity beforeExtent beforeBound maps fixups held exits next advance inbounds out kind byte accepted

end Itasca.Compiler

end

end

end
