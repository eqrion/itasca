import Itasca.Runtime.Code.Local.Checking.ScalarExitSlotBounds
import Itasca.Runtime.Code.Body.Reader.Common.ReaderSelectEmissions
import Itasca.Runtime.Code.Body.Reader.Global.ReaderGlobalEmissions
import Itasca.Runtime.Code.Body.Reader.Local.ReaderLocalEmissions
import Itasca.Runtime.Code.Body.Reader.Memory.ReaderMemoryEmissions
import Itasca.Runtime.Code.Body.Reader.Common.ReaderOrdinaryEffects
import Itasca.Runtime.Code.Local.Checking.LinearEmissionInstructionPrefix

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Actual source-typed local get reading preserves every stored instruction check. -/
theorem reader_local_get_open_instructions_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env .Wasm2 locals typeIndex st) {A : Type}
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
  have tables := (reader_local_get_effects ops law before after st.core out.core data env ctx
    (base_step_wasm2 _ (by decide) (by decide) rfl (by simp only [global_simps]; decide) (by simpa only [global_simps] using accepted))).tables
  exact ⟨lowered.1.linearInstructionPrefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed local set reading preserves every stored instruction check. -/
theorem reader_local_set_open_instructions_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env .Wasm2 locals typeIndex st) {A : Type}
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
  have tables := (reader_local_set_effects ops law before after st.core out.core data env ctx
    (base_step_wasm2 _ (by decide) (by decide) rfl (by simp only [global_simps]; decide) (by simpa only [global_simps] using accepted))).tables
  rw [input] at layout
  exact ⟨lowered.1.linearInstructionPrefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed local tee reading preserves every stored instruction check. -/
theorem reader_local_tee_open_instructions_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env .Wasm2 locals typeIndex st) {A : Type}
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
  have tables := (reader_local_tee_effects ops law before after st.core out.core data env ctx
    (base_step_wasm2 _ (by decide) (by decide) rfl (by simp only [global_simps]; decide) (by simpa only [global_simps] using accepted))).tables
  rw [input] at layout
  exact ⟨lowered.1.linearInstructionPrefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed global get reading preserves every stored instruction check. -/
theorem reader_global_get_open_instructions_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env .Wasm2 locals typeIndex st) {A : Type}
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
  have tables := (reader_global_get_effects ops law before after st.core out.core data env ctx
    (base_step_wasm2 _ (by decide) (by decide) rfl (by simp only [global_simps]; decide) (by simpa only [global_simps] using accepted))).tables
  exact ⟨lowered.1.floatCoreInstructionPrefix layout reachable localsMatch.symm emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed global set reading preserves every stored instruction check. -/
theorem reader_global_set_open_instructions_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env .Wasm2 locals typeIndex st) {A : Type}
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
  have tables := (reader_global_set_effects ops law before after st.core out.core data env ctx
    (base_step_wasm2 _ (by decide) (by decide) rfl (by simp only [global_simps]; decide) (by simpa only [global_simps] using accepted))).tables
  rw [input] at layout
  exact ⟨lowered.1.floatCoreInstructionPrefix layout reachable localsMatch.symm emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed select reading preserves every stored instruction check. -/
theorem reader_select_open_instructions_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env .Wasm2 locals typeIndex st) {A : Type}
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
  have tables := (reader_select_effects ops law before after st.core out.core data env ctx
    (base_step_wasm2 _ (by decide) (by decide) rfl (by simp only [global_simps]; decide) (by simpa only [global_simps] using accepted))).tables
  rw [input] at layout
  exact ⟨lowered.1.floatCoreInstructionPrefix layout reachable localsMatch.symm emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed memory load reading preserves every stored instruction check. -/
theorem reader_memory_load_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
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
  have tables := (reader_memory_load_effects_wasm2 ops law before after _ out data env ctx _ op accepted).tables
  rw [input] at layout
  exact ⟨lowered.1.floatCoreInstructionPrefix layout reachable contextLocalsCode emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual source-typed memory store reading preserves every stored instruction check. -/
theorem reader_memory_store_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
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
  have tables := (reader_memory_store_effects_wasm2 ops law before after _ out data env ctx _ op accepted).tables
  rw [input] at layout
  exact ⟨lowered.1.floatCoreInstructionPrefix layout reachable contextLocalsCode emission tables held stable.frames,stable.exit_slots exits⟩

end Itasca.Runtime.Code
