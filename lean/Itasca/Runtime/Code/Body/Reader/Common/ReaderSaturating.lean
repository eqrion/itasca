import Itasca.Runtime.Code.Body.Reader.Common.ReaderSignExtension
import Itasca.Runtime.Code.Local.Lowering.Float.FloatOpcode
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
theorem reader_saturating_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState) (ctx : code.Context) (subopcode : U32) (next : Usize)
    (operation : Numeric.Operation)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 0xfc#u8)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (meaning : Wasm2.NumericExtensions.saturatingMeaning subopcode = some operation)
    (accepted : code.step_extended visitor st.core data env ctx 0xfc#u8 before =
      .ok (.Ok (), out, after)) :
    code.visit_saturating visitor before out subopcode = .ok (.Ok (), after) ∧
      Numeric.read operation {st.core with pos := next} = .ok (.Ok (), out) ∧
      code.read_conversion {st.core with pos := next} operation.input operation.output = .ok (.Ok (), out) ∧
      out.ctrls = st.core.ctrls ∧ out.pos = next ∧
      ∃ values, StackSemantics.NumericEffect p.current.ctrl.polymorphic_base p.current.vals
          operation.inputs operation.output values ∧
        ReaderPostWasm2 p out operation.instruction p.current.ctrl.polymorphic_base values := by
  have readLeb := reader.read_u32_leb.complete data st.core.pos subopcode next decoded
  rw [code.step_extended.prefixed] at accepted
  simp only [Wasm2.prefixedStep, readLeb, bind_ok, meaning] at accepted
  obtain ⟨unit, converted, callback⟩ := reader_run_success _ _ _ _ _ accepted
  cases unit
  have unary := Wasm2.NumericExtensions.saturating_unary meaning
  have read : Numeric.read operation {st.core with pos := next} = .ok (.Ok (), out) := by
    simpa only [Numeric.read, unary, Bool.false_eq_true, ↓reduceIte] using converted
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have physicalBase : (Control.base {st.core with pos := next}).val = outer.length := by simp [Control.base, ctrls, base]
  have polymorphic : Control.polymorphic {st.core with pos := next} = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have effect := Numeric.read.segment operation {st.core with pos := next} outer p.current.vals vals physicalBase capacity
  rw [read, WP.spec_ok] at effect
  obtain ⟨controls, position, values, stack, length, numeric⟩ := effect
  dsimp only at controls position stack length numeric
  rw [polymorphic] at numeric
  refine ⟨callback, read, converted, controls, position, values, numeric, ?_⟩
  have encoded : Wasm2.At data p.start (.plain operation.instruction) out.pos := by
    obtain ⟨bytes, first, last, slice, leb⟩ := decoded
    apply Wasm2.At.of_immediate p.inbounds byte p.pos (.saturating subopcode operation meaning leb)
    simpa only [position] using (show Wasm1.BytesAt data st.core.pos bytes next from ⟨first, last, slice⟩)
  apply reader_append_wasm2 p out operation.instruction p.current.ctrl.polymorphic_base values
    operation.wellFormed encoded
    (fun C wf priorTyped => numeric.wasm2_prefix C wf p.current.ops operation.instruction priorTyped
      operation.wellFormed (operation.typed C wf))
  · simpa [controls] using ctrls
  · simpa [vals, base] using stack
  · exact Wasm2.NumericExtensions.saturating_declared meaning _

theorem float_saturating_reader_facts {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (op : Abs.Float.Instruction) (extension : 256 ≤ (floatOpcode op).val) :
    ∃ (subopcode : U32) (operation : Numeric.Operation) (hook : ExtendedNumericHook),
      subopcode.val = (floatOpcode op).val - 256 ∧ subopcode.val < 8 ∧
      Wasm2.NumericExtensions.saturatingMeaning subopcode = some operation ∧
      operation.instruction = op.source ∧
      operation.inputs.map Translate.valueType = List.replicate op.arity (valtype_numtype op.input) ∧
      Translate.valueType operation.output = valtype_numtype op.output ∧
      hook.encoding = (0xfc#u8, some subopcode) ∧
      invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler (.op state (.extendedNumeric hook)) =
        runtime.compiler.lower.FunctionCompiler.op ops compiler state (floatOpcode op) 0#u32 0#u32 0#u128 := by
  change 256 ≤ op.opcode at extension
  cases op with
  | unary ty operator => cases ty <;> cases operator <;> norm_num [Abs.Float.Instruction.opcode,Abs.Float.signIndex, Abs.Float.unaryIndex, Abs.Float.binaryIndex, Abs.Float.compareIndex] at extension
  | binary ty operator => cases ty <;> cases operator <;> norm_num [Abs.Float.Instruction.opcode,Abs.Float.signIndex, Abs.Float.unaryIndex, Abs.Float.binaryIndex, Abs.Float.compareIndex] at extension
  | compare ty operator => cases ty <;> cases operator <;> norm_num [Abs.Float.Instruction.opcode,Abs.Float.signIndex, Abs.Float.unaryIndex, Abs.Float.binaryIndex, Abs.Float.compareIndex] at extension
  | convert source target sign => cases source <;> cases target <;> cases sign <;> norm_num [Abs.Float.Instruction.opcode,Abs.Float.signIndex, Abs.Float.unaryIndex, Abs.Float.binaryIndex, Abs.Float.compareIndex] at extension
  | reinterpretFloat source => cases source <;> norm_num [Abs.Float.Instruction.opcode,Abs.Float.signIndex, Abs.Float.unaryIndex, Abs.Float.binaryIndex, Abs.Float.compareIndex] at extension
  | reinterpretInt source => cases source <;> norm_num [Abs.Float.Instruction.opcode,Abs.Float.signIndex, Abs.Float.unaryIndex, Abs.Float.binaryIndex, Abs.Float.compareIndex] at extension
  | promote | demote => skip <;> norm_num [Abs.Float.Instruction.opcode,Abs.Float.signIndex, Abs.Float.unaryIndex, Abs.Float.binaryIndex, Abs.Float.compareIndex] at extension
  | truncate source target sign saturating =>
    cases saturating with
    | false => cases source <;> cases target <;> cases sign <;> norm_num [Abs.Float.Instruction.opcode,Abs.Float.signIndex, Abs.Float.unaryIndex, Abs.Float.binaryIndex, Abs.Float.compareIndex] at extension
    | true =>
      cases source with
      | F32 =>
        cases target with
        | I32 =>
          cases sign with
          | S => exact ⟨0#u32, _, .i32_trunc_sat_f32_s, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩
          | U => exact ⟨1#u32, _, .i32_trunc_sat_f32_u, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩
        | I64 =>
          cases sign with
          | S => exact ⟨4#u32, _, .i64_trunc_sat_f32_s, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩
          | U => exact ⟨5#u32, _, .i64_trunc_sat_f32_u, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩
      | F64 =>
        cases target with
        | I32 =>
          cases sign with
          | S => exact ⟨2#u32, _, .i32_trunc_sat_f64_s, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩
          | U => exact ⟨3#u32, _, .i32_trunc_sat_f64_u, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩
        | I64 =>
          cases sign with
          | S => exact ⟨6#u32, _, .i64_trunc_sat_f64_s, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩
          | U => exact ⟨7#u32, _, .i64_trunc_sat_f64_u, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Saturating float lowering consumes the canonical complete LEB immediate
and advances the same pending source zipper as the actual profile reader. -/
theorem reader_float_saturating_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (op : Abs.Float.Instruction)
    (extension : 256 ≤ (floatOpcode op).val)
    (subopcode : U32) (next : Usize)
    (subopcodeEq : subopcode.val = (floatOpcode op).val - 256)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (byte : data.val[p.start.val]'p.inbounds = 0xfc#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 0xfc#u8 before = .ok (.Ok (),out,after)) :
    ∃ operation : Numeric.Operation,
      operation.instruction = op.source ∧
      operation.inputs.map Translate.valueType = List.replicate op.arity (valtype_numtype op.input) ∧
      Translate.valueType operation.output = valtype_numtype op.output ∧
      runtime.compiler.lower.FunctionCompiler.op ops before out.core (floatOpcode op) 0#u32 0#u32 0#u128 = .ok (.Ok (),after) ∧
      Numeric.read operation {st.core with pos := next} = .ok (.Ok (),out.core) ∧
      code.read_conversion {st.core with pos := next} operation.input operation.output = .ok (.Ok (),out.core) ∧
      out.core.ctrls = st.core.ctrls ∧ out.core.pos = next ∧
      ∃ values, StackSemantics.NumericEffect p.current.ctrl.polymorphic_base p.current.vals
        operation.inputs operation.output values ∧
        ReaderPostWasm2 p out.core op.source p.current.ctrl.polymorphic_base values := by
  obtain ⟨sub,operation,hook,subEq,bound,meaning,instruction,inputs,output,encoding,hookEq⟩ :=
    float_saturating_reader_facts ops before out.core op extension
  have same : sub = subopcode := (UScalar.eq_equiv _ _).mpr (subEq.trans subopcodeEq.symm)
  subst sub
  obtain ⟨capacity,run⟩ := profile_scalar_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index 0xfc#u8 before after (by decide) accepted
  rw [code.step_wasm2.saturating _ _ _ _ _ _ _ _ decoded bound] at run
  obtain ⟨callback,read,converted,controls,position,values,numeric,post⟩ :=
    reader_saturating_wasm2 p (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      before after out.core ctx subopcode next operation capacity byte decoded meaning run
  have dispatch := ExtendedNumericHook.dispatch (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before out.core hook
  rw [encoding] at dispatch
  dsimp only at dispatch
  rw [dispatch,hookEq] at callback
  exact ⟨operation,instruction,inputs,output,callback,read,converted,controls,position,values,numeric,instruction ▸ post⟩

end Itasca.Runtime.Code
