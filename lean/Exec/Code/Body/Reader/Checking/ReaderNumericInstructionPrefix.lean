import Exec.Code.Local.Checking.ScalarExitSlotBounds
import Exec.Code.Body.Reader.Common.ReaderNumericEmissions
import Exec.Code.Body.Reader.Common.ReaderSignEmissions
import Exec.Code.Body.Reader.Common.ReaderOrdinaryEffects
import Exec.Code.Local.Checking.LinearEmissionInstructionPrefix

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Actual typed integer reader progress preserves all stored instruction checks. -/
theorem reader_numeric_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : Abs.Numeric.Instruction) (baseOpcode : (integerOpcode op).val < 192)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,front,values,input,post,instruction,lowered,emission⟩ :=
    reader_emit_numeric_wasm2 p ops law before after out ctx contextLocals op baseOpcode known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_numeric_effects_wasm2 p ops law before after out ctx op byte accepted).tables
  rw [input] at layout
  exact ⟨lowered.1.linearInstructionPrefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

/-- Actual typed integer reader progress preserves all stored instruction checks. -/
theorem reader_sign_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : Abs.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,front,values,input,post,instruction,lowered,emission⟩ :=
    reader_emit_sign_wasm2 p ops law before after out ctx contextLocals op extension known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_numeric_effects_wasm2 p ops law before after out ctx op byte accepted).tables
  rw [input] at layout
  exact ⟨lowered.1.linearInstructionPrefix layout reachable emission tables held stable.frames,stable.exit_slots exits⟩

end Exec.Code
