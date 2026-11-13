import Itasca.Wasm2.LoopDispatch
import Itasca.Wasm2.Scalar.Env
import Itasca.Handler.Select
import Itasca.Binary.Wasm1.DeclaredReferences

/-!
Sections, each formerly its own module: ReaderPost, NumericReader, BasicReader, IndexReader.
-/

/-! ## ReaderPost -/

section

/-!
Exact source-prefix advancement shared by validator preservation and compiler replay.
`ReaderPost` retains the decoded instruction and the original frame zipper as well
as the ordinary `Pending.After` invariant.
-/

namespace Itasca.Wasm2
open Aeneas Aeneas.Std Itasca

/-- A reader advances this precise source zipper; source instructions are not
recovered from an unrelated existential post-state witness. -/
structure ReaderPost {data env locals index st}
    (pending : Pending data env locals index st) (out : code.OpIterState)
    (instruction : instr) (poly : Bool) (values : List code.StackType) : Prop where
  encoded : At data pending.start (.plain instruction) out.pos
  opened : Frames.Open env (bodyContext env locals pending.ft) {st with core := out}
    pending.parents (pending.current.advance (.plain instruction) instruction poly values)
  after : pending.After {st with core := out}

/-- Retain the exact decoded instruction under its original frame context. -/
theorem Pending.append_reader_context {data env locals index st}
    (p : Pending data env locals index st) (C : context) (outer : List code.StackType)
    (spine : Frames.Spine env (bodyContext env locals p.ft) p.parents C outer p.current.form p.current.ins)
    (header : Frames.Header env C p.current)
    (base : p.current.ctrl.value_stack_base.val = outer.length)
    (out : code.OpIterState) (instruction : instr) (poly : Bool) (values : List code.StackType)
    (wf : wf_instr instruction) (encoded : At data p.start (.plain instruction) out.pos)
    (typed : TypedPrefix (Frames.enter C p.current.form p.current.ins p.current.outs)
      ((p.current.form.params p.current.ins).map Translate.valueType)
      (p.current.ops ++ [instruction]) poly values)
    (controls : out.ctrls.val = p.parents.map Frames.Saved.ctrl ++ [{p.current.ctrl with polymorphic_base := poly}])
    (blocks : ({core := out} : code.BodyState).blocks.val = p.parents.map Frames.Saved.bt ++ [p.current.bt])
    (stack : out.vals.val = outer ++ values)
    (declared : DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) instruction) :
    Wasm2.ReaderPost p out instruction poly values := by
  refine ⟨encoded, ?_, ?_⟩
  · exact ⟨C, outer, spine, ⟨header.kind, header.inputs, header.outputs,
      header.prior, .simple header.emits (.plain instruction wf)⟩, base, typed, controls, blocks, stack⟩
  · exact p.append_result C outer spine header base {core := out} instruction poly values
      wf encoded typed controls blocks stack declared

/-- Append an independently encoded instruction to the same source zipper. -/
theorem Pending.append_reader {data env locals index st}
    (p : Pending data env locals index st) (out : code.OpIterState)
    (instruction : instr) (poly : Bool) (values : List code.StackType)
    (wf : wf_instr instruction) (encoded : At data p.start (.plain instruction) out.pos)
    (typed : ∀ C, wf_context C →
      TypedPrefix C ((p.current.form.params p.current.ins).map Translate.valueType)
        p.current.ops p.current.ctrl.polymorphic_base p.current.vals →
      TypedPrefix C ((p.current.form.params p.current.ins).map Translate.valueType)
        (p.current.ops ++ [instruction]) poly values)
    (controls : out.ctrls.val = p.parents.map Frames.Saved.ctrl ++
      [{p.current.ctrl with polymorphic_base := poly}])
    (stack : out.vals.val = st.core.vals.val.take p.current.ctrl.value_stack_base.val ++ values)
    (declared : DeclaredReferences.Instruction
      (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) instruction) :
    ReaderPost p out instruction poly values := by
  obtain ⟨C, outer, spine, header, base, priorTyped, ctrls, blocks, vals⟩ := p.opened
  have Cwf := Frames.enter_wf C (spine.context_wf (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have newTyped := typed _ Cwf priorTyped
  have newVals : out.vals.val = outer ++ values := by simpa [vals, base] using stack
  have newBlocks : ({st with core := out} : code.BodyState).blocks.val = p.parents.map Frames.Saved.bt ++ [p.current.bt] := by
    simpa [controls, ctrls] using blocks
  refine ⟨encoded, ?_, ?_⟩
  · exact ⟨C, outer, spine, ⟨header.kind, header.inputs, header.outputs,
      header.prior, .simple header.emits (.plain instruction wf)⟩, base, newTyped, controls, newBlocks, newVals⟩
  · exact p.append_result C outer spine header base {st with core := out} instruction poly values
      wf encoded newTyped controls newBlocks newVals declared

end Itasca.Wasm2

end

/-! ## NumericReader -/

section

/-!
Exact numeric-reader effects shared by scalar arithmetic, floating-point operations,
sign extensions, and saturating conversions. Opcode decoding supplies the source
encoding; this proof supplies the common operand and source-prefix preservation.
-/
namespace Itasca.Wasm2
open Aeneas Aeneas.Std Itasca

theorem Pending.numeric_reader {data env locals index st}
    (p : Pending data env locals index st) (operation : Numeric.Operation)
    (position : Usize) (capacity : st.core.vals.val.length < Usize.max)
    (encoded : At data p.start (.plain operation.instruction) position)
    (declared : DeclaredReferences.Instruction
      (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) operation.instruction) :
    Numeric.read operation {st.core with pos := position} ⦃ r =>
      r.2.ctrls = st.core.ctrls ∧ r.2.pos = position ∧
      ∀ unit, r.1 = .Ok unit → ∃ values,
        StackSemantics.NumericEffect p.current.ctrl.polymorphic_base p.current.vals
          operation.inputs operation.output values ∧
        ReaderPost p r.2 operation.instruction p.current.ctrl.polymorphic_base values ⦄ := by
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have physicalBase : (Control.base {st.core with pos := position}).val = outer.length := by
    simp [Control.base, ctrls, base]
  have polymorphic : Control.polymorphic {st.core with pos := position} = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  apply WP.spec_mono (Numeric.read.segment operation {st.core with pos := position}
    outer p.current.vals vals physicalBase capacity)
  rintro ⟨result,out⟩ ⟨controls,cursor,values,stack,_,numeric⟩
  dsimp only at controls cursor stack numeric ⊢
  refine ⟨controls,cursor,?_⟩
  intro unit accepted
  subst result
  rw [polymorphic] at numeric
  refine ⟨values,numeric,?_⟩
  refine p.append_reader out operation.instruction p.current.ctrl.polymorphic_base values
    operation.wellFormed (cursor ▸ encoded)
    (fun C wf prior => numeric.wasm2_prefix C wf p.current.ops operation.instruction prior
      operation.wellFormed (operation.typed C wf)) ?_ ?_ declared
  · simpa [controls] using ctrls
  · simpa [vals,base] using stack

end Itasca.Wasm2

end

/-! ## BasicReader -/

section

/-!
Reader facts for constants and terminal scalar instructions, shared by validator
preservation and compiler inversion. Each successful read retains the exact byte
encoding, stack effect, and advancement of the original source prefix. These
results make no assumption about visitor callbacks.
-/

namespace Itasca.Wasm2
open Aeneas Aeneas.Std Itasca

/-- NOP records its opcode while preserving the precise source stack. -/
theorem Pending.nop_reader {data env locals index st}
    (p : Pending data env locals index st)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_NOP) :
    ReaderPost p st.core .NOP p.current.ctrl.polymorphic_base p.current.vals := by
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  have encoded : Wasm1.At data p.start (.plain .NOP) st.core.pos :=
    .no_immediate p.inbounds (by simpa [global_simps] using byte) p.pos .nop
  apply p.append_reader st.core .NOP p.current.ctrl.polymorphic_base p.current.vals .instr_case_0
    (.plain encoded) (fun C wf priorTyped => priorTyped.nop wf) ?_ ?_ ?_
  · simpa using controls
  · simp [vals, base]
  · simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

/-- A successful i32 constant read retains its exact source prefix and stack effect. -/
theorem Pending.read_i32_const {data env locals index st}
    (p : Pending data env locals index st)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I32_CONST) :
    code.read_i32_const st.core data ⦃ r => ∀ value, r.1 = .Ok value →
      r.2.vals.val = st.core.vals.val ++ [.Val .I32] ∧
      ReaderPost p r.2 (Spec.i32Const value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .I32]) ⦄ := by
  apply WP.spec_mono (code.read_i32_const.spec st.core data capacity)
  rintro ⟨res, out⟩ ⟨controls, effect⟩ value accepted
  dsimp only at controls effect accepted ⊢
  subst res
  obtain ⟨decoded, values⟩ := effect
  refine ⟨values, ?_⟩
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have encoded : Wasm1.At data p.start (.plain (Spec.i32Const value)) out.pos :=
    .of_s32 value p.inbounds (by simpa [global_simps] using byte) p.pos decoded
  refine p.append_reader out (Spec.i32Const value) p.current.ctrl.polymorphic_base
    (p.current.vals ++ [.Val .I32]) (Spec.i32Const_wf value) (.plain encoded)
    (fun C wf priorTyped => priorTyped.i32Const wf value) ?_ ?_ ?_

  · simpa [controls] using ctrls
  · simpa [vals, base, List.append_assoc] using values
  · exact encoded.declared _

/-- A successful i64 constant read retains its exact source prefix and stack effect. -/
theorem Pending.read_i64_const {data env locals index st}
    (p : Pending data env locals index st)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I64_CONST) :
    code.read_i64_const st.core data ⦃ r => ∀ value, r.1 = .Ok value →
      r.2.vals.val = st.core.vals.val ++ [.Val .I64] ∧
      ReaderPost p r.2 (ScalarConst.i64 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .I64]) ⦄ := by
  apply WP.spec_mono (code.read_i64_const.spec st.core data capacity)
  rintro ⟨res, out⟩ ⟨controls, effect⟩ value accepted
  dsimp only at controls effect accepted ⊢
  subst res
  obtain ⟨decoded, values⟩ := effect
  refine ⟨values, ?_⟩
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have encoded : Wasm1.At data p.start (.plain (ScalarConst.i64 value)) out.pos :=
    .of_s64 value p.inbounds (by simpa [global_simps] using byte) p.pos decoded
  refine p.append_reader out (ScalarConst.i64 value) p.current.ctrl.polymorphic_base
    (p.current.vals ++ [.Val .I64]) (ScalarConst.i64_wf value) (.plain encoded)
    (fun C wf priorTyped => priorTyped.i64Const wf value) ?_ ?_ ?_

  · simpa [controls] using ctrls
  · simpa [vals, base, List.append_assoc] using values
  · exact encoded.declared _

/-- A successful f32 constant read retains its exact source prefix and stack effect. -/
theorem Pending.read_f32_const {data env locals index st}
    (p : Pending data env locals index st)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F32_CONST) :
    code.read_f32_const st.core data ⦃ r => ∀ value, r.1 = .Ok value →
      r.2.vals.val = st.core.vals.val ++ [.Val .F32] ∧
      ReaderPost p r.2 (ScalarConst.f32 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .F32]) ⦄ := by
  apply WP.spec_mono (code.read_f32_const.spec st.core data capacity)
  rintro ⟨res, out⟩ ⟨controls, effect⟩ value accepted
  dsimp only at controls effect accepted ⊢
  subst res
  obtain ⟨decoded, values⟩ := effect
  refine ⟨values, ?_⟩
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have encoded : Wasm1.At data p.start (.plain (ScalarConst.f32 value)) out.pos :=
    .of_f32 value p.inbounds (by simpa [global_simps] using byte) p.pos decoded
  refine p.append_reader out (ScalarConst.f32 value) p.current.ctrl.polymorphic_base
    (p.current.vals ++ [.Val .F32]) (ScalarConst.f32_wf value) (.plain encoded)
    (fun C wf priorTyped => priorTyped.f32Const wf value) ?_ ?_ ?_

  · simpa [controls] using ctrls
  · simpa [vals, base, List.append_assoc] using values
  · exact encoded.declared _

/-- A successful f64 constant read retains its exact source prefix and stack effect. -/
theorem Pending.read_f64_const {data env locals index st}
    (p : Pending data env locals index st)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F64_CONST) :
    code.read_f64_const st.core data ⦃ r => ∀ value, r.1 = .Ok value →
      r.2.vals.val = st.core.vals.val ++ [.Val .F64] ∧
      ReaderPost p r.2 (ScalarConst.f64 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .F64]) ⦄ := by
  apply WP.spec_mono (code.read_f64_const.spec st.core data capacity)
  rintro ⟨res, out⟩ ⟨controls, effect⟩ value accepted
  dsimp only at controls effect accepted ⊢
  subst res
  obtain ⟨decoded, values⟩ := effect
  refine ⟨values, ?_⟩
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have encoded : Wasm1.At data p.start (.plain (ScalarConst.f64 value)) out.pos :=
    .of_f64 value p.inbounds (by simpa [global_simps] using byte) p.pos decoded
  refine p.append_reader out (ScalarConst.f64 value) p.current.ctrl.polymorphic_base
    (p.current.vals ++ [.Val .F64]) (ScalarConst.f64_wf value) (.plain encoded)
    (fun C wf priorTyped => priorTyped.f64Const wf value) ?_ ?_ ?_

  · simpa [controls] using ctrls
  · simpa [vals, base, List.append_assoc] using values
  · exact encoded.declared _

/-- Unreachable trims the operand stack and advances the same source prefix. -/
theorem Pending.read_unreachable {data env locals index st}
    (p : Pending data env locals index st)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_UNREACHABLE) :
    code.read_unreachable st.core ⦃ r => r.1 = .Ok () ∧
      r.2.vals.val = st.core.vals.val.take p.current.ctrl.value_stack_base.val ∧
      ReaderPost p r.2 .UNREACHABLE true [] ⦄ := by
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  obtain ⟨marked, markedEq, markedVals, _, markedControls, markedPos⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec st.core (p.parents.map Frames.Saved.ctrl) p.current.ctrl controls
      (by simp [base, vals]))
  simp only [code.read_unreachable, markedEq, bind_ok, WP.spec_ok]
  refine ⟨trivial, markedVals, ?_⟩
  have encoded : Wasm1.At data p.start (.plain .UNREACHABLE) marked.pos :=
    .no_immediate p.inbounds (by simpa [global_simps] using byte)
      (by simpa [markedPos] using p.pos) .unreachable
  refine p.append_reader marked .UNREACHABLE true [] .instr_case_1 (.plain encoded)
    (fun C wf priorTyped => priorTyped.unreachable wf) markedControls ?_ ?_

  · simpa using markedVals
  · exact encoded.declared _

end Itasca.Wasm2

end

/-! ## IndexReader -/

section

/-!
Shared exact source-prefix advancement for local and global index readers.
The operand-reader certificate supplies typing and bytes; both validator forward
preservation and compiler inversion use this construction.
-/
namespace Itasca.Wasm2
open Aeneas Aeneas.Std Itasca

theorem Pending.index_reader_post {data env locals index st}
    (p : Pending data env locals index st) (C : context) (outer : List code.StackType)
    (spine : Frames.Spine env (bodyContext env locals p.ft) p.parents C outer p.current.form p.current.ins)
    (header : Frames.Header env C p.current)
    (base : p.current.ctrl.value_stack_base.val = outer.length)
    (ctrls : st.core.ctrls.val = p.parents.map Frames.Saved.ctrl ++ [p.current.ctrl])
    (blocks : st.blocks.val = p.parents.map Frames.Saved.bt ++ [p.current.bt])
    (opcode : U8) (instruction : U32 → instr)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (wf : ∀ idx, wf_instr (instruction idx))
    (immediate : ∀ idx bytes, Leb128.Encoding bytes idx.val → Wasm1.Immediate opcode (.plain (instruction idx)) bytes)
    (out : code.OpIterState) (idx : U32)
    (post : Scalar.IndexPost ((p.current.form.params p.current.ins).map Translate.valueType)
      data st.core outer p.current.vals (Frames.enter C p.current.form p.current.ins p.current.outs)
      p.current.ops instruction (.Ok idx, out)) :
    ∃ values, out.vals.val = outer ++ values ∧
      Wasm2.ReaderPost p out (instruction idx) p.current.ctrl.polymorphic_base values := by
  obtain ⟨decoded, controls, values, stack, length, typed⟩ := post idx rfl
  dsimp only at decoded controls stack length typed
  have polymorphic : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic, ctrls]
  have encoded : Wasm1.At data p.start (.plain (instruction idx)) out.pos := by
    obtain ⟨bytes, start, length, span, encoding⟩ := decoded
    exact .of_immediate p.inbounds byte p.pos (immediate idx bytes encoding) ⟨start, length, span⟩
  refine ⟨values, stack, ?_⟩
  refine Wasm2.Pending.append_reader_context p C outer spine header base out (instruction idx)
    p.current.ctrl.polymorphic_base values (wf idx) (.plain encoded)
    (by simpa [polymorphic] using typed) ?_ ?_ ?_ ?_

  · simpa [controls] using ctrls
  · simpa [controls] using blocks
  · exact stack
  · exact encoded.declared _

end Itasca.Wasm2

end
