import Itasca.Runtime.Code.Body.Reader.Checking.ReaderDeadOperationInstructionPrefix
import Itasca.Runtime.Code.Body.Reader.Checking.ReaderNumericInstructionPrefix
import Itasca.Runtime.Code.Body.Reader.Float.ReaderFloatInstructionPrefix
import Itasca.Runtime.Code.Body.Reader.Checking.ReaderCoreInstructionPrefix
import Itasca.Runtime.Code.Body.Control.Table.StructuredCompilerPrefix

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Source-prefix geometry supplies live operation checks; dead reading only observes. -/
theorem reader_numeric_checked_prefix_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (contextSource : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (op : Abs.Numeric.Instruction) (baseOpcode : (integerOpcode op).val < 192)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  by_cases live : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live live
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    exact reader_numeric_open_instructions_wasm2 p ops law before after out ctx contextSource op baseOpcode (invariant.known live) (monomorphic live) retained.layout live
      codeFits sourceFits coordinateFits held exits byte accepted
  · exact reader_dead_numeric_checked_prefix_wasm2 p ops law before after out ctx contextSource (Bool.eq_false_iff.mpr live) op baseOpcode held exits byte accepted

/-- Source-prefix geometry supplies live operation checks; dead reading only observes. -/
theorem reader_float_checked_prefix_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
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
    (op : Abs.Float.Instruction) (baseOpcode : (floatOpcode op).val < 256)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (floatOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (floatOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  by_cases live : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live live
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    exact reader_float_open_instructions_wasm2 p ops law before after out ctx contextSource op C (contextLocals.trans retained.localsEq.symm) baseOpcode (invariant.known live) (monomorphic live) retained.layout live
      codeFits sourceFits coordinateFits held exits byte accepted
  · exact reader_dead_float_checked_prefix_wasm2 p ops law before after out ctx contextSource (Bool.eq_false_iff.mpr live) op baseOpcode held exits byte accepted

/-- Source-prefix geometry supplies live operation checks; dead reading only observes. -/
theorem reader_memory_load_checked_prefix_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (contextSource : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (C : context) (contextLocals : C.LOCALS = locals)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (op : Abs.Memory.Load)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryLoadOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (memoryLoadOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  by_cases live : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live live
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    exact reader_memory_load_open_instructions_wasm2 p ops law before after out ctx contextSource op C (contextLocals.trans retained.localsEq.symm) contextMemories (invariant.known live) (monomorphic live) retained.layout live
      codeFits sourceFits coordinateFits held exits byte accepted
  · exact reader_dead_memory_load_checked_prefix_wasm2 p ops law before after out ctx contextSource (Bool.eq_false_iff.mpr live) op held exits byte accepted

/-- Source-prefix geometry supplies live operation checks; dead reading only observes. -/
theorem reader_memory_store_checked_prefix_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (contextSource : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (C : context) (contextLocals : C.LOCALS = locals)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (op : Abs.Memory.Store)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryStoreOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (memoryStoreOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  by_cases live : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live live
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    exact reader_memory_store_open_instructions_wasm2 p ops law before after out ctx contextSource op C (contextLocals.trans retained.localsEq.symm) contextMemories (invariant.known live) (monomorphic live) retained.layout live
      codeFits sourceFits coordinateFits held exits byte accepted
  · exact reader_dead_memory_store_checked_prefix_wasm2 p ops law before after out ctx contextSource (Bool.eq_false_iff.mpr live) op held exits byte accepted

/-- Source-prefix geometry supplies live operation checks; dead reading only observes. -/
theorem reader_sign_checked_prefix_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (contextSource : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (op : Abs.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  by_cases live : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live live
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    exact reader_sign_open_instructions_wasm2 p ops law before after out ctx contextSource op extension (invariant.known live) (monomorphic live) retained.layout live
      codeFits sourceFits coordinateFits held exits byte accepted
  · exact reader_dead_sign_checked_prefix_wasm2 p ops law before after out ctx (Bool.eq_false_iff.mpr live) op extension held exits byte accepted

/-- Source-prefix geometry supplies live operation checks; dead reading only observes. -/
theorem reader_saturating_checked_prefix_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
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
    (op : Abs.Float.Instruction) (extension : 256 ≤ (floatOpcode op).val) (subopcode : U32) (next : Usize)
    (subopcodeEq : subopcode.val = (floatOpcode op).val-256)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 0xfc#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (0xfc#u8) before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  by_cases live : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live live
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    exact reader_saturating_open_instructions_wasm2 p ops law before after out ctx contextSource op C (contextLocals.trans retained.localsEq.symm) extension subopcode next subopcodeEq decoded (invariant.known live) (monomorphic live) retained.layout live
      codeFits sourceFits coordinateFits held exits byte accepted
  · exact reader_dead_saturating_checked_prefix_wasm2 p ops law before after out ctx contextSource (Bool.eq_false_iff.mpr live) op extension subopcode next subopcodeEq decoded held exits byte accepted

end Itasca.Runtime.Code
