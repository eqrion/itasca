import Itasca.Runtime.Code.Local.Checking.ScalarExitSlotBounds
import Itasca.Runtime.Code.Body.Reader.Float.ReaderFloatEmissions
import Itasca.Runtime.Code.Body.Reader.Common.ReaderSaturatingEmissions
import Itasca.Runtime.Code.Body.Reader.Common.ReaderOrdinaryEffects
import Itasca.Runtime.Code.Local.Checking.CoreEmissionInstructionPrefix

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Actual typed floating-point reader progress preserves all stored instruction checks. -/
theorem reader_float_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : Abs.Float.Instruction) (C : context)
    (contextLocalsCode : C.LOCALS = compilerLocals before) (baseOpcode : (floatOpcode op).val < 256)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (floatOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (floatOpcode op)) before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,front,values,input,post,instruction,lowered,emission⟩ :=
    reader_emit_float_wasm2 p ops law before after out ctx contextLocals op C contextLocalsCode baseOpcode known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_float_base_effects_wasm2 ops law before after _ out data env ctx _ op baseOpcode accepted).tables
  rw [input] at layout
  exact ⟨lowered.1.floatCoreInstructionPrefix layout reachable contextLocalsCode emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual typed floating-point reader progress preserves all stored instruction checks. -/
theorem reader_saturating_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : Abs.Float.Instruction) (C : context)
    (contextLocalsCode : C.LOCALS = compilerLocals before) (extension : 256 ≤ (floatOpcode op).val)
    (subopcode : U32) (next : Usize)
    (subopcodeEq : subopcode.val = (floatOpcode op).val - 256)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 0xfc#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (0xfc#u8) before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,front,values,input,post,instruction,lowered,emission⟩ :=
    reader_emit_saturating_wasm2 p ops law before after out ctx contextLocals op C contextLocalsCode extension subopcode next subopcodeEq decoded known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_saturating_effects_wasm2 p ops law before after out ctx op extension subopcode next subopcodeEq decoded byte accepted).tables
  rw [input] at layout
  exact ⟨lowered.1.floatCoreInstructionPrefix layout reachable contextLocalsCode emission tables held stable.frames,stable.exit_slots exits⟩

end Itasca.Runtime.Code
