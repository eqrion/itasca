import Exec.Code.Local.Checking.ScalarExitSlotBounds
import Exec.Code.Body.Reader.Common.ReaderSelectEmissions
import Exec.Code.Body.Reader.Global.ReaderGlobalEmissions
import Exec.Code.Body.Reader.Local.ReaderLocalEmissions
import Exec.Code.Body.Reader.Memory.ReaderMemoryEmissions
import Exec.Code.Body.Reader.Table.ReaderLiteralTables
import Exec.Code.Body.Reader.Table.ReaderLiteralTablesWasm1
import Exec.Code.Body.Reader.Table.ReaderCoreTables
import Exec.Code.Body.Reader.Table.ReaderCoreTablesWasm1
import Exec.Code.Local.Checking.LinearEmissionInstructionPrefix

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Actual source-typed local get reading preserves every stored instruction check. -/
theorem reader_local_get_open_instructions_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (localsMatch : before.function.locals = ctx.locals)
    (types : List types.ValueType) (concrete : st.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 32#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOCAL_GET before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,index,ty,values,found,post,instruction,lowered,emission⟩ :=
    reader_emit_local_get_wasm1 p ops law before after out localsMatch types concrete layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := reader_local_get_tables_wasm1 ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  exact ⟨lowered.1.linearInstructionPrefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed local set reading preserves every stored instruction check. -/
theorem reader_local_set_open_instructions_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (localsMatch : before.function.locals = ctx.locals)
    (known : ConcreteStack st.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 33#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOCAL_SET before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,index,ty,values,front,found,input,post,instruction,lowered,emission⟩ :=
    reader_emit_local_set_wasm1 p ops law before after out localsMatch known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := reader_local_set_tables_wasm1 ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  rw [input] at layout
  exact ⟨lowered.1.linearInstructionPrefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed local tee reading preserves every stored instruction check. -/
theorem reader_local_tee_open_instructions_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (localsMatch : before.function.locals = ctx.locals)
    (known : ConcreteStack st.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 34#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOCAL_TEE before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,index,ty,values,front,found,input,post,instruction,lowered,emission⟩ :=
    reader_emit_local_tee_wasm1 p ops law before after out localsMatch known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := reader_local_tee_tables_wasm1 ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  rw [input] at layout
  exact ⟨lowered.1.linearInstructionPrefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed global get reading preserves every stored instruction check. -/
theorem reader_global_get_open_instructions_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (C : context) (localsMatch : compilerLocals before = C.LOCALS)
    (globalsMatch : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (types : List types.ValueType) (concrete : st.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 35#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_GLOBAL_GET before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,index,ty,values,found,post,instruction,lowered,emission⟩ :=
    reader_emit_global_get_wasm1 p ops law before after out C localsMatch globalsMatch types concrete layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := reader_global_get_tables_wasm1 ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  exact ⟨lowered.1.floatCoreInstructionPrefix layout reachable localsMatch.symm (.core emission) tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed global set reading preserves every stored instruction check. -/
theorem reader_global_set_open_instructions_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (C : context) (localsMatch : compilerLocals before = C.LOCALS)
    (globalsMatch : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (known : ConcreteStack st.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 36#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_GLOBAL_SET before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,index,ty,values,front,found,mutable,input,post,instruction,lowered,emission⟩ :=
    reader_emit_global_set_wasm1 p ops law before after out C localsMatch globalsMatch known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := reader_global_set_tables_wasm1 ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  rw [input] at layout
  exact ⟨lowered.1.floatCoreInstructionPrefix layout reachable localsMatch.symm (.core emission) tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed select reading preserves every stored instruction check. -/
theorem reader_select_open_instructions_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (C : context) (localsMatch : compilerLocals before = C.LOCALS)
    (known : ConcreteStack st.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 27#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_SELECT before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,ty,front,values,input,post,instruction,lowered,emission⟩ :=
    reader_emit_select_wasm1 p ops law before after out C localsMatch known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := reader_select_tables_wasm1 ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  rw [input] at layout
  exact ⟨lowered.1.floatCoreInstructionPrefix layout reachable localsMatch.symm (.core emission) tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed memory load reading preserves every stored instruction check. -/
theorem reader_memory_load_open_instructions_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (op : Abs.Memory.Load) (C : context)
    (contextLocalsCode : C.LOCALS = compilerLocals before)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (known : ConcreteStack st.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryLoadOpcode op))
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (memoryLoadOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,arg,front,values,input,post,instruction,lowered,emission⟩ :=
    reader_emit_memory_load_wasm1 p ops law before after out op C contextLocalsCode contextMemories known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := reader_memory_load_tables_wasm1 p ops law before after out op byte accepted
  rw [input] at layout
  exact ⟨lowered.1.floatCoreInstructionPrefix layout reachable contextLocalsCode (.core emission) tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed memory store reading preserves every stored instruction check. -/
theorem reader_memory_store_open_instructions_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (op : Abs.Memory.Store) (C : context)
    (contextLocalsCode : C.LOCALS = compilerLocals before)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (known : ConcreteStack st.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryStoreOpcode op))
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (memoryStoreOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,arg,front,values,input,post,instruction,lowered,emission⟩ :=
    reader_emit_memory_store_wasm1 p ops law before after out op C contextLocalsCode contextMemories known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := reader_memory_store_tables_wasm1 p ops law before after out op byte accepted
  rw [input] at layout
  exact ⟨lowered.1.floatCoreInstructionPrefix layout reachable contextLocalsCode (.core emission) tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed local get reading preserves every stored instruction check. -/
theorem reader_local_get_open_instructions_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (localsMatch : before.function.locals = locals)
    (types : List types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 32#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex .Wasm2 code.OP_LOCAL_GET before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,index,ty,values,found,post,instruction,lowered,emission⟩ :=
    reader_emit_local_get_wasm2 p ops law before after out ctx contextLocals localsMatch types concrete layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := reader_local_get_tables_wasm2 ops law before after st out data env ctx typeIndex (by simpa only [global_simps] using accepted)
  exact ⟨lowered.1.linearInstructionPrefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed local set reading preserves every stored instruction check. -/
theorem reader_local_set_open_instructions_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (localsMatch : before.function.locals = locals)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 33#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex .Wasm2 code.OP_LOCAL_SET before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,index,ty,values,front,found,input,post,instruction,lowered,emission⟩ :=
    reader_emit_local_set_wasm2 p ops law before after out ctx contextLocals localsMatch known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := reader_local_set_tables_wasm2 ops law before after st out data env ctx typeIndex (by simpa only [global_simps] using accepted)
  rw [input] at layout
  exact ⟨lowered.1.linearInstructionPrefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed local tee reading preserves every stored instruction check. -/
theorem reader_local_tee_open_instructions_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (localsMatch : before.function.locals = locals)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 34#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex .Wasm2 code.OP_LOCAL_TEE before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,index,ty,values,front,found,input,post,instruction,lowered,emission⟩ :=
    reader_emit_local_tee_wasm2 p ops law before after out ctx contextLocals localsMatch known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := reader_local_tee_tables_wasm2 ops law before after st out data env ctx typeIndex (by simpa only [global_simps] using accepted)
  rw [input] at layout
  exact ⟨lowered.1.linearInstructionPrefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed global get reading preserves every stored instruction check. -/
theorem reader_global_get_open_instructions_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (C : context) (localsMatch : compilerLocals before = C.LOCALS)
    (globalsMatch : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (types : List types.ValueType) (concrete : st.core.vals.val = types.map code.StackType.Val)
    (layout : CompilerLayout before (types.map Translate.valueType))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 35#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex .Wasm2 code.OP_GLOBAL_GET before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,index,ty,values,found,post,instruction,lowered,emission⟩ :=
    reader_emit_global_get_wasm2 p ops law before after out ctx contextLocals C localsMatch globalsMatch types concrete layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := reader_global_get_tables_wasm2 ops law before after st out data env ctx typeIndex (by simpa only [global_simps] using accepted)
  exact ⟨lowered.1.floatCoreInstructionPrefix layout reachable localsMatch.symm (.core emission) tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed global set reading preserves every stored instruction check. -/
theorem reader_global_set_open_instructions_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (C : context) (localsMatch : compilerLocals before = C.LOCALS)
    (globalsMatch : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 36#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex .Wasm2 code.OP_GLOBAL_SET before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,index,ty,values,front,found,mutable,input,post,instruction,lowered,emission⟩ :=
    reader_emit_global_set_wasm2 p ops law before after out ctx contextLocals C localsMatch globalsMatch known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := reader_global_set_tables_wasm2 ops law before after st out data env ctx typeIndex (by simpa only [global_simps] using accepted)
  rw [input] at layout
  exact ⟨lowered.1.floatCoreInstructionPrefix layout reachable localsMatch.symm (.core emission) tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed select reading preserves every stored instruction check. -/
theorem reader_select_open_instructions_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (C : context) (localsMatch : compilerLocals before = C.LOCALS)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 27#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex .Wasm2 code.OP_SELECT before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,ty,front,values,input,post,instruction,lowered,emission⟩ :=
    reader_emit_select_wasm2 p ops law before after out ctx contextLocals C localsMatch known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := reader_select_tables_wasm2 ops law before after st out data env ctx typeIndex (by simpa only [global_simps] using accepted)
  rw [input] at layout
  exact ⟨lowered.1.floatCoreInstructionPrefix layout reachable localsMatch.symm (.core emission) tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed memory load reading preserves every stored instruction check. -/
theorem reader_memory_load_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : Abs.Memory.Load) (C : context)
    (contextLocalsCode : C.LOCALS = compilerLocals before)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryLoadOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (memoryLoadOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,arg,front,values,input,post,instruction,lowered,emission⟩ :=
    reader_emit_memory_load_wasm2 p ops law before after out ctx contextLocals op C contextLocalsCode contextMemories known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := reader_memory_load_tables_wasm2 p ops law before after out ctx contextLocals op byte accepted
  rw [input] at layout
  exact ⟨lowered.1.floatCoreInstructionPrefix layout reachable contextLocalsCode (.core emission) tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed memory store reading preserves every stored instruction check. -/
theorem reader_memory_store_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : Abs.Memory.Store) (C : context)
    (contextLocalsCode : C.LOCALS = compilerLocals before)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryStoreOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (memoryStoreOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,arg,front,values,input,post,instruction,lowered,emission⟩ :=
    reader_emit_memory_store_wasm2 p ops law before after out ctx contextLocals op C contextLocalsCode contextMemories known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := reader_memory_store_tables_wasm2 p ops law before after out ctx contextLocals op byte accepted
  rw [input] at layout
  exact ⟨lowered.1.floatCoreInstructionPrefix layout reachable contextLocalsCode (.core emission) tables held stable.frames,stable.exit_slots exits⟩

end Exec.Code
