import Exec.Code.Body.Reader.Checking.ReaderScalarInstructionPrefixWasm1
import Exec.Code.Body.Reader.Checking.ReaderOperationInstructionPrefix
import Exec.Code.Body.Reader.Checking.ReaderTypedSelectCheckedPrefix
import Exec.Code.Body.Reader.Checking.ReaderStatefulInstructionPrefix
import Exec.Code.Body.Reader.Memory.ReaderMemoryMetadataIndirectWasm1
import Exec.Code.Body.Reader.Common.StatefulReaderBase
import Exec.Code.Body.Reader.Common.StatefulReaderBulkDispatch
import Exec.Code.Body.Reader.Common.ReaderMiscAccepted
import Exec.Code.Body.Reader.Source.SourceOpcodeFamilies
import Exec.Code.Body.Reader.Simd.ReaderSimdEventDispatch
import Exec.Code.Body.Reader.Simd.ReaderSimdInstructionPrefix

namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

private theorem integer_extension_byte_high (op : Abs.Numeric.Instruction)
    (extension : 192 ≤ (integerOpcode op).val) : 192 ≤ (UScalar.cast .U8 (integerOpcode op)).val := by
  have bound := integerOpcode_byte op
  scalar_tac

private theorem base_opcode_rejected {V : Type} (source : code.OpVisitor V)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (before after : V)
    (absent : (6 ≤ opcode.val ∧ opcode.val ≤ 10) ∨ (18 ≤ opcode.val ∧ opcode.val ≤ 25) ∨
      (28 ≤ opcode.val ∧ opcode.val ≤ 31) ∨ (37 ≤ opcode.val ∧ opcode.val ≤ 39) ∨ 192 ≤ opcode.val)
    (accepted : code.step source st data env ctx opcode before = .ok (.Ok (),out,after)) : False := by
  by_cases high : 192 ≤ opcode.val
  · have missing : Numeric.opcodeMeaning opcode = none := by
      cases meaning : Numeric.opcodeMeaning opcode with
      | none => rfl
      | some operation => have bound := Numeric.NumericOp.bounds meaning; omega
    rw [code.step.numeric_dispatch source st data env ctx opcode before (by omega),
      code.step_numeric.unrecognized source st opcode before missing] at accepted
    simp at accepted
  · rw [code.step.reserved source st data env ctx opcode before (by tauto)] at accepted
    simp at accepted

/-- Source opcode coverage composes every noncontrol Wasm 2 reader family,
including unreachable code, bulk operations, typed select, and all scalar numeric and memory forms.
The excluded control cases have separate source-frame adapters. -/
theorem reader_noncontrol_checked_prefix_wasm1 {jumpTables : List U32} {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (C : context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial before types functions returns locals
      parents current st.vals.val p.start.val)
    (localsMatch : before.function.locals = ctx.locals)
    (matched : EnvTranslation.Matches env ctx C)
    (contextLocals : C.LOCALS = locals)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (opcode : U8) (noncontrol : opcode.val ∉ [2,3,4,5,11,12,13,14,15,16,17])
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  cases source_opcode_family opcode with
  | scalar kind same =>
    rw [same] at byte accepted noncontrol
    exact reader_scalar_checked_prefix_wasm1 p ops law initial before after out C invariant localsMatch
      contextLocals matched.globals monomorphic sourceBound bodyBound kind held exits byte accepted
  | integer op base same =>
    rw [same] at byte accepted noncontrol
    exact reader_numeric_checked_prefix_wasm1 p ops law initial before after out invariant
      monomorphic sourceBound bodyBound op base held exits byte accepted
  | float op base same =>
    rw [same] at byte accepted noncontrol
    exact reader_float_checked_prefix_wasm1 p ops law initial before after out invariant C contextLocals
      monomorphic sourceBound bodyBound op base held exits byte accepted
  | sign op extension same =>
    have high : 192 ≤ opcode.val := by rw [same]; exact integer_extension_byte_high op extension
    exact False.elim (base_opcode_rejected (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st out data env ctx opcode before after (by omega) accepted)
  | load op same =>
    rw [same] at byte accepted noncontrol
    exact reader_memory_load_checked_prefix_wasm1 p ops law initial before after out invariant C contextLocals
      matched.mems monomorphic sourceBound bodyBound op held exits byte accepted
  | store op same =>
    rw [same] at byte accepted noncontrol
    exact reader_memory_store_checked_prefix_wasm1 p ops law initial before after out invariant C contextLocals
      matched.mems monomorphic sourceBound bodyBound op held exits byte accepted
  | typedSelect same =>
    have value := congrArg UScalar.val same
    exact False.elim (base_opcode_rejected (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st out data env ctx opcode before after (by rw [same]; decide) accepted)
  | stateful member =>
    by_cases memory : opcode.val ∈ [63,64]
    · obtain ⟨op,single,arguments,callback,post⟩ := reader_stateful_memory_wasm1 p
        (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out opcode memory byte accepted
      rw [stateful_callback_lower ops before out op 0#u32 0#u32 arguments] at callback
      exact post.instruction_prefix ops law initial before after C invariant monomorphic matched contextLocals
        0#u32 0#u32 single arguments callback sourceBound bodyBound held exits
    · exact False.elim (base_opcode_rejected (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st out data env ctx opcode before after (by simp only [List.mem_cons,List.not_mem_nil,or_false] at member memory; omega) accepted)
  | misc same | simd same =>
    have value := congrArg UScalar.val same
    exact False.elim (base_opcode_rejected (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st out data env ctx opcode before after (by rw [same]; decide) accepted)
  | control kind same =>
    rw [same] at byte accepted noncontrol
    cases kind <;> simp [ControlReaderKind.opcode,global_simps] at noncontrol
  | table same =>
    rw [same] at byte accepted noncontrol
    simp at noncontrol
  | reserved rejected =>
    exact False.elim (base_opcode_rejected (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st out data env ctx opcode before after (by have absent := rejected.absent; tauto) accepted)

end Exec.Code
