import Exec.Code.Body.Reader.Checking.ReaderScalarInstructionPrefixWasm2
import Exec.Code.Body.Reader.Checking.ReaderOperationInstructionPrefix
import Exec.Code.Body.Reader.Checking.ReaderTypedSelectCheckedPrefix
import Exec.Code.Body.Reader.Checking.ReaderStatefulInstructionPrefix
import Exec.Code.Body.Reader.Common.StatefulReaderBase
import Exec.Code.Body.Reader.Common.StatefulReaderBulkDispatch
import Exec.Code.Body.Reader.Common.ReaderMiscAccepted
import Exec.Code.Body.Reader.Source.SourceOpcodeFamilies
import Exec.Code.Body.Reader.Simd.ReaderSimdEventDispatch
import Exec.Code.Body.Reader.Simd.ReaderSimdInstructionPrefix

namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Source opcode coverage composes every noncontrol Wasm 2 reader family,
including unreachable code, bulk operations, typed select, and all SIMD forms.
The excluded control cases have separate source-frame adapters. -/
theorem reader_noncontrol_checked_prefix_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
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
      st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
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

end Exec.Code
