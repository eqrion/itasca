import Exec.Code.Local.Lowering.Common.NumericOpcode
import Exec.Code.Local.Relations.Common.Rel
import Exec.Code.Body.Reader.Common.ReaderWasm2
import Exec.Code.Body.Reader.Common.ReaderProfile
import Itasca.Wasm2.NumericExt.Sound
import Itasca.Visitor.EventTables
set_option maxHeartbeats 1000000
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Exact sign-extension reading advances the supplied source zipper and
retains both the physical conversion and actual visitor callback. -/
theorem reader_sign_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState) (ctx : code.Context) (opcode : U8)
    (operation : Numeric.Operation)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (meaning : Wasm2.NumericExtensions.signMeaning opcode = some operation)
    (accepted : code.step_extended visitor st.core data env ctx opcode before =
      .ok (.Ok (), out, after)) :
    code.visit_sign_extension visitor before out opcode = .ok (.Ok (), after) ∧
      Numeric.read operation st.core = .ok (.Ok (), out) ∧
      code.read_conversion st.core operation.input operation.output = .ok (.Ok (), out) ∧
      out.ctrls = st.core.ctrls ∧ out.pos = st.core.pos ∧
      ∃ values, StackSemantics.NumericEffect p.current.ctrl.polymorphic_base p.current.vals
          operation.inputs operation.output values ∧
        ReaderPostWasm2 p out operation.instruction p.current.ctrl.polymorphic_base values := by
  rw [code.step_extended.sign visitor st.core data env ctx opcode operation before meaning] at accepted
  obtain ⟨unit, converted, callback⟩ := reader_run_success _ _ _ _ _ accepted
  cases unit
  have unary := (Wasm2.NumericExtensions.sign_properties meaning).1
  have read : Numeric.read operation st.core = .ok (.Ok (), out) := by
    simpa only [Numeric.read, unary, Bool.false_eq_true, ↓reduceIte] using converted
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have physicalBase : (Control.base st.core).val = outer.length := by simp [Control.base, ctrls, base]
  have polymorphic : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have effect := Numeric.read.segment operation st.core outer p.current.vals vals physicalBase capacity
  rw [read, WP.spec_ok] at effect
  obtain ⟨controls, position, values, stack, length, numeric⟩ := effect
  dsimp only at controls position stack length numeric
  rw [polymorphic] at numeric
  refine ⟨callback, read, converted, controls, position, values, numeric, ?_⟩
  have encoded : Wasm2.At data p.start (.plain operation.instruction) out.pos :=
    Wasm2.At.of_immediate p.inbounds byte p.pos (.signExtension opcode operation meaning)
      (by simpa only [position] using (Wasm1.BytesAt.nil data st.core.pos
        (by have := p.pos; have := p.inbounds; omega)))
  apply reader_append_wasm2 p out operation.instruction p.current.ctrl.polymorphic_base values
    operation.wellFormed encoded
    (fun C wf priorTyped => numeric.wasm2_prefix C wf p.current.ops operation.instruction priorTyped
      operation.wellFormed (operation.typed C wf))
  · simpa [controls] using ctrls
  · simpa [vals, base] using stack
  · exact Wasm2.NumericExtensions.sign_declared meaning _

/-- The five Wasm2 sign extensions match their canonical operation and visitor
hook, and invoke the ordinary integer lowering entry with their exact opcode. -/
theorem integer_sign_reader_facts {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (op : Abs.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val) :
    ∃ (operation : Numeric.Operation) (hook : ExtendedNumericHook),
      Wasm2.NumericExtensions.signMeaning (UScalar.cast .U8 (integerOpcode op)) = some operation ∧
      operation.instruction = op.source ∧
      operation.inputs.map Translate.valueType = List.replicate op.arity (integerType op.input) ∧
      Translate.valueType operation.output = integerType op.output ∧
      hook.encoding = (UScalar.cast .U8 (integerOpcode op), none) ∧
      invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler (.op state (.extendedNumeric hook)) =
        runtime.compiler.lower.FunctionCompiler.op ops compiler state (integerOpcode op) 0#u32 0#u32 0#u128 ∧
      (UScalar.cast .U8 (integerOpcode op)).val ∉ Wasm2.controlOpcodes ∧
      (UScalar.cast .U8 (integerOpcode op)).val ∉ [28, 37, 38, 208, 209, 210, 252, 253] := by
  cases op with
  | binary ty operator =>
    cases ty <;> cases operator <;> (try (rename_i sign; cases sign)) <;>
      norm_num [integerOpcode] at extension
  | compare ty operator =>
    cases ty <;> cases operator <;> (try (rename_i sign; cases sign)) <;>
      norm_num [integerOpcode] at extension
  | unary ty operator =>
    cases ty with
    | I32 =>
      cases operator with
      | clz | ctz | popcnt => norm_num [integerOpcode] at extension
      | extend8 => exact ⟨_, .i32_extend8_s, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide⟩
      | extend16 => exact ⟨_, .i32_extend16_s, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide⟩
    | I64 =>
      cases operator with
      | clz | ctz | popcnt => norm_num [integerOpcode] at extension
      | extend8 => exact ⟨_, .i64_extend8_s, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide⟩
      | extend16 => exact ⟨_, .i64_extend16_s, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide⟩
      | extend32 => exact ⟨_, .i64_extend32_s, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide⟩
  | eqz ty => cases ty <;> norm_num [integerOpcode] at extension
  | conversion operator => cases operator <;> norm_num [integerOpcode] at extension

/-- Successful profile dispatch for any of the five sign extensions supplies
all reader capacity, hook identity and exact source-position facts internally. -/
theorem reader_integer_sign_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (op : Abs.Numeric.Instruction)
    (extension : 192 ≤ (integerOpcode op).val)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    ∃ operation : Numeric.Operation,
      operation.instruction = op.source ∧
      operation.inputs.map Translate.valueType = List.replicate op.arity (integerType op.input) ∧
      Translate.valueType operation.output = integerType op.output ∧
      runtime.compiler.lower.FunctionCompiler.op ops before out.core (integerOpcode op) 0#u32 0#u32 0#u128 =
        .ok (.Ok (), after) ∧
      Numeric.read operation st.core = .ok (.Ok (), out.core) ∧
      code.read_conversion st.core operation.input operation.output = .ok (.Ok (), out.core) ∧
      out.core.ctrls = st.core.ctrls ∧ out.core.pos = st.core.pos ∧
      ∃ values, StackSemantics.NumericEffect p.current.ctrl.polymorphic_base p.current.vals
          operation.inputs operation.output values ∧
        ReaderPostWasm2 p out.core op.source p.current.ctrl.polymorphic_base values := by
  obtain ⟨operation, hook, meaning, instruction, inputs, output, encoding, hookEq, ordinary, base⟩ :=
    integer_sign_reader_facts ops before out.core op extension
  obtain ⟨capacity, run⟩ := profile_scalar_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index _ before after ordinary accepted
  rw [code.step_wasm2.base _ _ _ _ _ _ _ base] at run
  obtain ⟨callback, read, converted, controls, position, values, numeric, post⟩ :=
    reader_sign_wasm2 p (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      before after out.core ctx _ operation capacity byte meaning run
  have dispatch := ExtendedNumericHook.dispatch
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before out.core hook
  rw [encoding] at dispatch
  dsimp only at dispatch
  rw [dispatch, hookEq] at callback
  exact ⟨operation, instruction, inputs, output, callback, read, converted, controls, position,
    values, numeric, instruction ▸ post⟩

end Exec.Code
