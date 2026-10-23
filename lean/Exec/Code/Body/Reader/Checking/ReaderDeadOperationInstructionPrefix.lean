import Exec.Code.Body.Reader.Common.ReaderSignExtension
import Exec.Code.Body.Callbacks.Common.CompilerPrefix
import Exec.Code.Local.Callbacks.Common.CompilerDeadMetadata
import Exec.Code.Local.Source.SourceCursor
import Exec.Code.Local.Relations.Common.DeadCode
import Exec.Code.Body.Reader.Common.ReaderSpan
import Exec.Code.Body.Reader.Common.ReaderProfile
import Exec.Code.Local.Relations.Common.KnownPopStack
import Exec.Code.Local.Relations.Common.KnownNumericStack
import Exec.Code.Body.Reader.Common.NumericReaderFacts
import Exec.Code.Local.Control.Common.Structured
import Exec.Code.Local.Control.Common.StructuredComposition
import Exec.Code.Local.Relations.Common.Concatenation
import Exec.Code.Local.Relations.Common.Extension
import Exec.Code.Local.Relations.Common.PrefixZipper
import Exec.Code.Local.Relations.Common.Prefix
import Exec.Code.Local.Relations.Common.ResolvedPrefix
import Exec.Code.Local.Control.Common.UniversalPrefix
import Exec.Code.Local.Control.Common.UniversalTerminal
import Exec.Code.Local.Control.Common.UniversalDormant
import Exec.Code.Body.Reader.Float.FloatReaderFacts
import Exec.Code.Body.Reader.Memory.MemoryReaderFacts
import Exec.Code.Local.Relations.Common.CoreLoweringEffects
import Exec.Code.Body.Reader.Common.ReaderValues
import Exec.Code.Local.Lowering.Common.LoweringArithmetic
import Exec.Code.Body.Reader.Common.ReaderSaturating
import Exec.Code.Local.Checking.DeadInstructionPrefix

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Actual unreachable numeric reading preserves both maintained checks. -/
theorem reader_dead_numeric_checked_prefix_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (dead : before.reachable = false)
    (op : Abs.Numeric.Instruction) (standard : (integerOpcode op).val < 192)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨operation, hook, meaning, handler, instruction, inputs, output,
    hookEq, ordinary, baseOpcode, sign, misc⟩ := integer_reader_facts ops before out.core op standard
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index _ before after ordinary baseOpcode sign misc contextLocals accepted
  obtain ⟨callback, read, _, _, values, effect, post⟩ := reader_numeric_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ operation hook
    capacity byte meaning handler run
  rw [hookEq] at callback
  exact compiler_dead_op_checked_prefix ops law before after out.core (integerOpcode op) 0#u32 0#u32 0#u128 dead held exits callback

/-- Actual unreachable float reading preserves both maintained checks. -/
theorem reader_dead_float_checked_prefix_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (dead : before.reachable = false)
    (op : Abs.Float.Instruction) (standard : (floatOpcode op).val < 256)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (floatOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (floatOpcode op)) before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨operation, hook, meaning, handler, instruction, inputs, output,
    hookEq, ordinary, baseOpcode, sign, misc⟩ := float_reader_facts ops before out.core op standard
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index _ before after ordinary baseOpcode sign misc contextLocals accepted
  obtain ⟨callback, read, _, _, values, effect, post⟩ := reader_numeric_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ operation hook
    capacity byte meaning handler run
  rw [hookEq] at callback
  exact compiler_dead_op_checked_prefix ops law before after out.core (floatOpcode op) 0#u32 0#u32 0#u128 dead held exits callback

/-- Actual unreachable memory load reading preserves both maintained checks. -/
theorem reader_dead_memory_load_checked_prefix_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (dead : before.reachable = false) (op : Abs.Memory.Load)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryLoadOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (memoryLoadOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨meaning,_,_,_,_,ordinary,base,sign,misc⟩ := memory_load_reader_facts ops before out.core op ⟨0#u32,0#u32⟩
  obtain ⟨capacity,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals,p.ft.results⟩ index _ before after ordinary base sign misc contextLocals accepted
  obtain ⟨arg,values,callback,read,post⟩ := reader_memory_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ (memoryLoadMeaning op)
    capacity byte meaning run
  obtain ⟨_,_,_,source,callbackEq,_⟩ := memory_load_reader_facts ops before out.core op arg
  rw [callbackEq] at callback
  rw [source] at post
  exact compiler_dead_op_checked_prefix ops law before after out.core (memoryLoadOpcode op) arg.offset arg.align 0#u128 dead held exits callback

/-- Actual unreachable memory store reading preserves both maintained checks. -/
theorem reader_dead_memory_store_checked_prefix_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (dead : before.reachable = false) (op : Abs.Memory.Store)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryStoreOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (memoryStoreOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨meaning,_,_,_,_,ordinary,base,sign,misc⟩ := memory_store_reader_facts ops before out.core op ⟨0#u32,0#u32⟩
  obtain ⟨capacity,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals,p.ft.results⟩ index _ before after ordinary base sign misc contextLocals accepted
  obtain ⟨arg,values,callback,read,post⟩ := reader_memory_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ (memoryStoreMeaning op)
    capacity byte meaning run
  obtain ⟨_,_,_,source,callbackEq,_⟩ := memory_store_reader_facts ops before out.core op arg
  rw [callbackEq] at callback
  rw [source] at post
  exact compiler_dead_op_checked_prefix ops law before after out.core (memoryStoreOpcode op) arg.offset arg.align 0#u128 dead held exits callback

/-- Actual unreachable saturating reading preserves both maintained checks. -/
theorem reader_dead_saturating_checked_prefix_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (dead : before.reachable = false)
    (op : Abs.Float.Instruction) (extension : 256 ≤ (floatOpcode op).val)
    (subopcode : U32) (next : Usize)
    (subopcodeEq : subopcode.val = (floatOpcode op).val - 256)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 0xfc#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (0xfc#u8) before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨operation,instruction,inputs,output,callback,_,_,_,_,values,effect,post⟩ :=
    reader_float_saturating_wasm2 p ops before after out ctx op extension subopcode next subopcodeEq decoded byte accepted
  exact compiler_dead_op_checked_prefix ops law before after out.core (floatOpcode op) 0#u32 0#u32 0#u128 dead held exits callback

/-- Sign-extension reading in dead code only observes the returned stack. -/
theorem reader_dead_sign_checked_prefix_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (dead : before.reachable = false) (op : Abs.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨operation,instruction,inputs,output,callback,_⟩ := reader_integer_sign_wasm2 p ops before after out ctx op extension byte accepted
  exact compiler_dead_op_checked_prefix ops law before after out.core (integerOpcode op) 0#u32 0#u32 0#u128 dead held exits callback

end Exec.Code
