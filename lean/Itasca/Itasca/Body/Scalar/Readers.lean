import Itasca.Body.Step.ScalarContext
import Itasca.Body.Complete.ScalarBase
import Itasca.Body.LoopDispatch
import Itasca.Body.Scalar.Env
import Itasca.Handler.ScalarOperations
import Itasca.Binary.Scalar.MemoryMeaning

open WebAssembly

/-!
Proofs for Body / Scalar.

This module collects Complete, Readers, Step.
Each section documents its contracts and consumers.
-/

/-! ## Complete -/

section

/-!
# Scalar completeness

`scalar_complete` shows that the shared `code.step` arms for non-control opcodes accept every
independently encoded scalar instruction at its principal typing under a Wasm 2.0 environment. It
reuses the scalar leaf completeness proofs, which place no restriction on the frame's arity.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

/-- Every independently encoded scalar instruction accepts its principal
SpecTec typing. This imposes neither a scalar environment restriction nor a
restriction on the active frame's input or output arity. -/
theorem scalar_complete (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (C : context) (st : code.OpIterState) (f : Body.Scalar.Completeness.Frame st) (opcode : U8)
    (op : instr) (bytes : List U8) (next : Usize) (front input output : List valtype)
    (hc : Translation.Environment.Matches env ctx C) (hsize : st.vals.val.length < Usize.max)
    (hscalar : opcode.val ∉ controlOpcodes)
    (hi : Body.Scalar.Immediate opcode (.plain op) bytes) (hb : Body.Scalar.BytesAt data st.pos bytes next)
    (hr : Body.Stack.Realizes f.current.polymorphic_base f.operands (front ++ input))
    (ht : Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output))) :
    Body.Scalar.Completeness.StepResult f data env ctx opcode next (front ++ output) := by
  cases hi with
  | unreachable => exact Body.Scalar.Completeness.unreachable f hb ht
  | nop => exact Body.Scalar.Completeness.nop f hb ht hr
  | br | brIf | brTable | return_ | call | callIndirect =>
      simp [controlOpcodes] at hscalar
  | drop => exact f.step_drop data env ctx next C front input output hb ht hr
  | select => exact f.step_select data env ctx next C front input output hb hsize ht hr
  | localGet idx he => exact Body.Scalar.Completeness.local_get f data env ctx C hc idx _ next he hb front input output ht hr hsize
  | localSet idx he => exact Body.Scalar.Completeness.local_set f data env ctx C hc idx _ next he hb front input output ht hr
  | localTee idx he => exact Body.Scalar.Completeness.local_tee f data env ctx C hc idx _ next he hb front input output ht hr hsize
  | globalGet idx he => exact Body.Scalar.Completeness.global_get f data env ctx C hc idx _ next he hb front input output ht hr hsize
  | globalSet idx he => exact Body.Scalar.Completeness.global_set f data env ctx C hc idx _ next he hb front input output ht hr
  | memory opcode operation arg hmap ha ho =>
      exact Body.Scalar.Completeness.memory f data env ctx C hc opcode operation hmap arg _ _ next ha ho hb
        front input output ht hr hsize
  | memorySize => exact Body.Scalar.Completeness.memory_size f data env ctx C hc next hb front input output ht hr hsize
  | memoryGrow => exact Body.Scalar.Completeness.memory_grow f data env ctx C hc next hb front input output ht hr hsize
  | i32Const value he => exact f.step_i32_const data env ctx value _ next C front input output he hb hsize ht hr
  | i64Const value he => exact f.step_i64_const data env ctx value _ next C front input output he hb hsize ht hr
  | f32Const value he => exact f.step_f32_const data env ctx value _ next C front input output he hb hsize ht hr
  | f64Const value he => exact f.step_f64_const data env ctx value _ next C front input output he hb hsize ht hr
  | numericInstruction opcode source hmap =>
    change Body.Numeric.opcodeInstruction opcode = _ at hmap
    rw [Body.Numeric.opcodeInstruction_eq] at hmap
    obtain ⟨operation, decoded, rfl⟩ := Option.map_eq_some_iff.mp hmap
    exact f.step_numeric data env ctx opcode operation next C front input output decoded hb hsize ht hr

end Itasca.Body

end

/-! ## Readers -/

section

/-!
Proofs for Body / Scalar.

This module collects IndexReader, StackReader, MemoryReader.
Each section documents its contracts and consumers.
-/

/-! ## IndexReader -/

section

/-! ## ReaderPost -/

section

/-!
Exact source-prefix advancement shared by validator preservation and compiler replay.
`ReaderPost` retains the decoded instruction and the original frame zipper as well
as the ordinary `Pending.After` invariant.
-/

namespace Itasca.Body
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
      ((p.current.form.params p.current.ins).map Translation.valueType)
      (p.current.ops ++ [instruction]) poly values)
    (controls : out.ctrls.val = p.parents.map Frames.Saved.ctrl ++ [{p.current.ctrl with polymorphic_base := poly}])
    (blocks : ({core := out} : code.BodyState).blocks.val = p.parents.map Frames.Saved.bt ++ [p.current.bt])
    (stack : out.vals.val = outer ++ values)
    (declared : Spec.DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) instruction) :
    Body.ReaderPost p out instruction poly values := by
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
      TypedPrefix C ((p.current.form.params p.current.ins).map Translation.valueType)
        p.current.ops p.current.ctrl.polymorphic_base p.current.vals →
      TypedPrefix C ((p.current.form.params p.current.ins).map Translation.valueType)
        (p.current.ops ++ [instruction]) poly values)
    (controls : out.ctrls.val = p.parents.map Frames.Saved.ctrl ++
      [{p.current.ctrl with polymorphic_base := poly}])
    (stack : out.vals.val = st.core.vals.val.take p.current.ctrl.value_stack_base.val ++ values)
    (declared : Spec.DeclaredReferences.Instruction
      (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) instruction) :
    ReaderPost p out instruction poly values := by
  obtain ⟨C, outer, spine, header, base, priorTyped, ctrls, blocks, vals⟩ := p.opened
  have Cwf := Frames.enter_wf C (spine.context_wf (Translation.Environment.context_wf env ⟨locals, p.ft.results⟩))
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

end Itasca.Body

end

/-! ## NumericReader -/

section

/-!
Exact numeric-reader effects shared by scalar arithmetic, floating-point operations,
sign extensions, and saturating conversions. Opcode decoding supplies the source
encoding; this proof supplies the common operand and source-prefix preservation.
-/
namespace Itasca.Body
open Aeneas Aeneas.Std Itasca

theorem Pending.numeric_reader {data env locals index st}
    (p : Pending data env locals index st) (operation : Body.Numeric.Operation)
    (position : Usize) (capacity : st.core.vals.val.length < Usize.max)
    (encoded : At data p.start (.plain operation.instruction) position)
    (declared : Spec.DeclaredReferences.Instruction
      (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) operation.instruction) :
    Body.Numeric.read operation {st.core with pos := position} ⦃ r =>
      r.2.ctrls = st.core.ctrls ∧ r.2.pos = position ∧
      ∀ unit, r.1 = .Ok unit → ∃ values,
        Body.Stack.Semantics.NumericEffect p.current.ctrl.polymorphic_base p.current.vals
          operation.inputs operation.output values ∧
        ReaderPost p r.2 operation.instruction p.current.ctrl.polymorphic_base values ⦄ := by
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have physicalBase : (Body.Control.base {st.core with pos := position}).val = outer.length := by
    simp [Body.Control.base, ctrls, base]
  have polymorphic : Body.Control.polymorphic {st.core with pos := position} = p.current.ctrl.polymorphic_base := by
    simp [Body.Control.polymorphic, ctrls]
  apply WP.spec_mono (Body.Numeric.read.segment operation {st.core with pos := position}
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
    (fun C wf prior => numeric.prefix C wf p.current.ops operation.instruction prior
      operation.wellFormed (operation.typed C wf)) ?_ ?_ declared
  · simpa [controls] using ctrls
  · simpa [vals,base] using stack

end Itasca.Body

end

/-! ## BasicReader -/

section

/-!
Reader facts for constants and terminal scalar instructions, shared by validator
preservation and compiler inversion. Each successful read retains the exact byte
encoding, stack effect, and advancement of the original source prefix. These
results make no assumption about visitor callbacks.
-/

namespace Itasca.Body
open Aeneas Aeneas.Std Itasca

/-- NOP records its opcode while preserving the precise source stack. -/
theorem Pending.nop_reader {data env locals index st}
    (p : Pending data env locals index st)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_NOP) :
    ReaderPost p st.core .NOP p.current.ctrl.polymorphic_base p.current.vals := by
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  have encoded : Body.Scalar.At data p.start (.plain .NOP) st.core.pos :=
    .no_immediate p.inbounds (by simp [global_simps] at byte; exact byte) p.pos .nop
  apply p.append_reader st.core .NOP p.current.ctrl.polymorphic_base p.current.vals .instr_case_0
    (.plain encoded) (fun C wf priorTyped => priorTyped.nop wf) ?_ ?_ ?_
  · simpa using controls
  · simp [vals, base]
  · simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]

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
  have encoded : Body.Scalar.At data p.start (.plain (Spec.i32Const value)) out.pos :=
    .of_s32 value p.inbounds (by simpa [global_simps] using byte) p.pos decoded
  refine p.append_reader out (Spec.i32Const value) p.current.ctrl.polymorphic_base
    (p.current.vals ++ [.Val .I32]) (Spec.i32_const_wf value) (.plain encoded)
    (fun C wf priorTyped => priorTyped.i32_const wf value) ?_ ?_ ?_

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
      ReaderPost p r.2 (Spec.Constants.i64 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .I64]) ⦄ := by
  apply WP.spec_mono (code.read_i64_const.spec st.core data capacity)
  rintro ⟨res, out⟩ ⟨controls, effect⟩ value accepted
  dsimp only at controls effect accepted ⊢
  subst res
  obtain ⟨decoded, values⟩ := effect
  refine ⟨values, ?_⟩
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have encoded : Body.Scalar.At data p.start (.plain (Spec.Constants.i64 value)) out.pos :=
    .of_s64 value p.inbounds (by simpa [global_simps] using byte) p.pos decoded
  refine p.append_reader out (Spec.Constants.i64 value) p.current.ctrl.polymorphic_base
    (p.current.vals ++ [.Val .I64]) (Spec.Constants.i64_wf value) (.plain encoded)
    (fun C wf priorTyped => priorTyped.i64_const wf value) ?_ ?_ ?_

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
      ReaderPost p r.2 (Spec.Constants.f32 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .F32]) ⦄ := by
  apply WP.spec_mono (code.read_f32_const.spec st.core data capacity)
  rintro ⟨res, out⟩ ⟨controls, effect⟩ value accepted
  dsimp only at controls effect accepted ⊢
  subst res
  obtain ⟨decoded, values⟩ := effect
  refine ⟨values, ?_⟩
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have encoded : Body.Scalar.At data p.start (.plain (Spec.Constants.f32 value)) out.pos :=
    .of_f32 value p.inbounds (by simpa [global_simps] using byte) p.pos decoded
  refine p.append_reader out (Spec.Constants.f32 value) p.current.ctrl.polymorphic_base
    (p.current.vals ++ [.Val .F32]) (Spec.Constants.f32_wf value) (.plain encoded)
    (fun C wf priorTyped => priorTyped.f32_const wf value) ?_ ?_ ?_

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
      ReaderPost p r.2 (Spec.Constants.f64 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .F64]) ⦄ := by
  apply WP.spec_mono (code.read_f64_const.spec st.core data capacity)
  rintro ⟨res, out⟩ ⟨controls, effect⟩ value accepted
  dsimp only at controls effect accepted ⊢
  subst res
  obtain ⟨decoded, values⟩ := effect
  refine ⟨values, ?_⟩
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have encoded : Body.Scalar.At data p.start (.plain (Spec.Constants.f64 value)) out.pos :=
    .of_f64 value p.inbounds (by simpa [global_simps] using byte) p.pos decoded
  refine p.append_reader out (Spec.Constants.f64 value) p.current.ctrl.polymorphic_base
    (p.current.vals ++ [.Val .F64]) (Spec.Constants.f64_wf value) (.plain encoded)
    (fun C wf priorTyped => priorTyped.f64_const wf value) ?_ ?_ ?_

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
  have encoded : Body.Scalar.At data p.start (.plain .UNREACHABLE) marked.pos :=
    .no_immediate p.inbounds (by simp [global_simps] at byte; exact byte)
      (by simpa [markedPos] using p.pos) .unreachable
  refine p.append_reader marked .UNREACHABLE true [] .instr_case_1 (.plain encoded)
    (fun C wf priorTyped => priorTyped.unreachable wf) markedControls ?_ ?_

  · simpa using markedVals
  · exact encoded.declared _

end Itasca.Body

end

/-! ## IndexReader -/

section

/-!
Shared exact source-prefix advancement for local and global index readers.
The operand-reader certificate supplies typing and bytes; both validator forward
preservation and compiler inversion use this construction.
-/
namespace Itasca.Body
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
    (immediate : ∀ idx bytes, Binary.Leb128.Encoding bytes idx.val → Body.Scalar.Immediate opcode (.plain (instruction idx)) bytes)
    (out : code.OpIterState) (idx : U32)
    (post : Itasca.Body.Scalar.IndexPost ((p.current.form.params p.current.ins).map Translation.valueType)
      data st.core outer p.current.vals (Frames.enter C p.current.form p.current.ins p.current.outs)
      p.current.ops instruction (.Ok idx, out)) :
    ∃ values, out.vals.val = outer ++ values ∧
      Body.ReaderPost p out (instruction idx) p.current.ctrl.polymorphic_base values := by
  obtain ⟨decoded, controls, values, stack, length, typed⟩ := post idx rfl
  dsimp only at decoded controls stack length typed
  have polymorphic : Body.Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Body.Control.polymorphic, ctrls]
  have encoded : Body.Scalar.At data p.start (.plain (instruction idx)) out.pos := by
    obtain ⟨bytes, start, length, span, encoding⟩ := decoded
    exact .of_immediate p.inbounds byte p.pos (immediate idx bytes encoding) ⟨start, length, span⟩
  refine ⟨values, stack, ?_⟩
  refine Body.Pending.append_reader_context p C outer spine header base out (instruction idx)
    p.current.ctrl.polymorphic_base values (wf idx) (.plain encoded)
    (by simpa [polymorphic] using typed) ?_ ?_ ?_ ?_

  · simpa [controls] using ctrls
  · simpa [controls] using blocks
  · exact stack
  · exact encoded.declared _

end Itasca.Body

end

end

/-! ## StackReader -/

section

/-!
Shared exact source-prefix and operand facts for drop and untyped select.
Validator preservation and compiler inversion project the same reader result,
including polymorphic operands and the concrete/bottom select result.
-/
namespace Itasca.Body
open Aeneas Aeneas.Std Itasca

theorem Pending.read_drop {data env locals index st}
    (p : Pending data env locals index st)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_DROP) :
    code.read_drop st.core ⦃ r => ∀ value, r.1 = .Ok value → ∃ values,
      Body.Stack.Semantics.Popped p.current.ctrl.polymorphic_base p.current.vals value values ∧
      ReaderPost p r.2 .DROP p.current.ctrl.polymorphic_base values ⦄ := by
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have physicalBase : (Body.Control.base st.core).val = outer.length := by simp [Body.Control.base, ctrls, base]
  have polymorphic : Body.Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Body.Control.polymorphic, ctrls]
  apply WP.spec_mono (code.pop_stack_type.segment st.core outer p.current.vals vals physicalBase)
  rintro ⟨res,out⟩ ⟨controls, position, values, stack, effect⟩ value accepted
  dsimp only at controls position stack effect accepted ⊢
  subst res
  change Body.Stack.Semantics.Popped (Body.Control.polymorphic st.core) p.current.vals value values at effect
  rw [polymorphic] at effect
  refine ⟨values, effect, ?_⟩
  have encoded : Body.Scalar.At data p.start (.plain .DROP) out.pos :=
    .no_immediate p.inbounds (by simp [global_simps] at byte; exact byte)
      (by simpa [position] using p.pos) .drop
  refine p.append_reader out .DROP p.current.ctrl.polymorphic_base values .instr_case_2 (.plain encoded)
    (fun C wf prior => effect.prefix_drop C wf p.current.ops prior) ?_ ?_ (encoded.declared _)

  · simpa [controls] using ctrls
  · simpa [vals, base] using stack

theorem Pending.read_select {data env locals index st}
    (p : Pending data env locals index st)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_SELECT) :
    code.read_select st.core ⦃ r => ∀ value, r.1 = .Ok value → ∃ values,
      Body.Stack.Semantics.SelectEffect p.current.ctrl.polymorphic_base p.current.vals value values ∧
      ReaderPost p r.2 (.SELECT none) p.current.ctrl.polymorphic_base values ⦄ := by
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have physicalBase : (Body.Control.base st.core).val = outer.length := by simp [Body.Control.base, ctrls, base]
  have polymorphic : Body.Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Body.Control.polymorphic, ctrls]
  apply WP.spec_mono (code.read_select.segment st.core outer p.current.vals vals physicalBase capacity)
  rintro ⟨res,out⟩ ⟨controls, position, values, stack, _, effect⟩ value accepted
  dsimp only at controls position stack effect accepted ⊢
  subst res
  change Body.Stack.Semantics.SelectEffect (Body.Control.polymorphic st.core) p.current.vals value values at effect
  rw [polymorphic] at effect
  refine ⟨values, effect, ?_⟩
  have encoded : Body.Scalar.At data p.start (.plain (.SELECT none)) out.pos :=
    .no_immediate p.inbounds (by simp [global_simps] at byte; exact byte)
      (by simpa [position] using p.pos) .select
  refine p.append_reader out (.SELECT none) p.current.ctrl.polymorphic_base values (.instr_case_3 _) (.plain encoded)
    (fun C wf prior => effect.prefix C wf p.current.ops prior) ?_ ?_ (encoded.declared _)

  · simpa [controls] using ctrls
  · simpa [vals, base] using stack

end Itasca.Body

end

/-! ## MemoryReader -/

section

/-! ## Memory -/

section

/-!
# Memory readers

Typed-prefix specs of the extracted `code.read_load`, `code.read_store`, `code.read_memory_size`
and `code.read_memory_grow` against the Wasm 2.0 `TypedPrefix` zipper. `MemoryPost` and
`ReservedPost` are their shared postconditions for memory arguments and reserved bytes.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Scalar

/-- Successful memory instructions expose the decoded alignment and offset, the unchanged frames,
and the typed operand segment. -/
def MemoryPost (inputs : List valtype) (data : Slice U8) (st : code.OpIterState)
    (outer segment : List code.StackType) (C : context) (ops : List instr)
    (op : code.MemArg → instr)
    (r : core.result.Result code.MemArg error.OpError × code.OpIterState) : Prop :=
  ∀ arg, r.1 = .Ok arg →
    (∃ middle, Binary.Leb128.Decoded data st.pos arg.align middle ∧
      Binary.Leb128.Decoded data middle arg.offset r.2.pos) ∧ r.2.ctrls = st.ctrls ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length + 1 ∧
        Body.TypedPrefix C inputs (ops ++ [op arg]) (Body.Control.polymorphic st) rest

/-- Successful `memory.size` and `memory.grow` expose the consumed zero reserved byte, the
unchanged frames, and the typed operand segment. -/
def ReservedPost (inputs : List valtype) (data : Slice U8) (st : code.OpIterState)
    (outer segment : List code.StackType) (C : context) (ops : List instr)
    (op : instr) (r : core.result.Result Unit error.OpError × code.OpIterState) : Prop :=
  r.1 = .Ok () →
    (∃ hp : st.pos.val < data.length, data.val[st.pos.val] = 0#u8 ∧ r.2.pos.val = st.pos.val + 1) ∧
    r.2.ctrls = st.ctrls ∧ ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length + 1 ∧
      Body.TypedPrefix C inputs (ops ++ [op]) (Body.Control.polymorphic st) rest

end Itasca.Body.Scalar

namespace Itasca

theorem code.read_load.prefix {inputs : List valtype} (st : code.OpIterState) (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment) (hbase : (Body.Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (C : context) (hC : Translation.Environment.Matches env ctx C) (ops : List instr)
    (htyped : Body.TypedPrefix C inputs ops (Body.Control.polymorphic st) segment)
    (opcode : U8) (operation : Body.MemoryMeaning.Operation)
    (hrow : Body.MemoryMeaning.opcodeMeaning opcode = some operation) (hload : operation.store = false) :
    code.read_load st data env operation.ty operation.naturalAlign ⦃
      Body.Scalar.MemoryPost inputs data st outer segment C ops operation.op ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hout⟩ := WP.spec_imp_exists (code.read_memarg.spec st data)
  dsimp only at hv hc hout
  cases r with
  | Err e =>
      simp [code.read_load, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Body.Scalar.MemoryPost]
  | Ok arg =>
      obtain ⟨rcheck, hcheck, hcheckpost⟩ := WP.spec_imp_exists
        (code.check_memory_and_alignment.spec env arg operation.naturalAlign)
      cases rcheck with
      | Err e =>
          simp [code.read_load, hr, hcheck, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Body.Scalar.MemoryPost]
      | Ok u =>
          obtain ⟨⟨r', s'⟩, hp, hc', hpos, rest, hv', hlen, hout'⟩ := WP.spec_imp_exists
            (code.pop_with_type.realizes s outer segment .I32 (by simpa [hv] using hvals)
              (by simpa [Body.Control.base, hc] using hbase))
          dsimp only at hc' hpos hv' hlen hout'
          cases r' with
          | Err e =>
              simp [code.read_load, hr, hcheck, hp, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Body.Scalar.MemoryPost]
          | Ok popped =>
              have hcap : s'.vals.val.length < Usize.max := by
                simp only [hv', hvals, List.length_append] at *
                omega
              obtain ⟨s'', hpush, hv'', hc'', hpos'⟩ := WP.spec_imp_exists
                (code.push_val.spec s' (.Val operation.ty) hcap)
              have hpop : ∀ ts, Body.Stack.Realizes (Body.Control.polymorphic st) rest ts →
                  Body.Stack.Realizes (Body.Control.polymorphic st) segment (ts ++ [.I32]) := by
                simpa [Body.Control.polymorphic, hc, Translation.valueType] using hout'.2
              obtain ⟨hwf, hop⟩ := hC.memory_operation opcode operation hrow arg hcheckpost.1 hcheckpost.2
              have htyping := (Body.ResumePrefix.after_pop htyped hpop).finish hC.wf
                (operation.op arg) [operation.ty] hwf
                (by simpa [Body.MemoryMeaning.Operation.inputs, Body.MemoryMeaning.Operation.outputs, hload,
                  Translation.valueType] using hop)
              rw [WP.spec_equiv_exists]
              refine ⟨(.Ok arg, s''), ?_, ?_⟩
              · simp [code.read_load, hr, hcheck, hp, hpush, core.result.Result.Insts.CoreOpsTry.branch]
              · intro a heq
                cases heq
                refine ⟨?_, hc''.trans (hc'.trans hc), rest ++ [.Val operation.ty],
                  ?_, by simpa using Nat.add_le_add_right hlen 1, by simpa using htyping⟩
                · simpa [hpos', hpos] using hout
                · simpa [hv', List.append_assoc] using hv''

theorem code.read_store.prefix {inputs : List valtype} (st : code.OpIterState) (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment) (hbase : (Body.Control.base st).val = outer.length)
    (C : context) (hC : Translation.Environment.Matches env ctx C) (ops : List instr)
    (htyped : Body.TypedPrefix C inputs ops (Body.Control.polymorphic st) segment)
    (opcode : U8) (operation : Body.MemoryMeaning.Operation)
    (hrow : Body.MemoryMeaning.opcodeMeaning opcode = some operation) (hstore : operation.store = true) :
    code.read_store st data env operation.ty operation.naturalAlign ⦃
      Body.Scalar.MemoryPost inputs data st outer segment C ops operation.op ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hout⟩ := WP.spec_imp_exists (code.read_memarg.spec st data)
  dsimp only at hv hc hout
  cases r with
  | Err e =>
      simp [code.read_store, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Body.Scalar.MemoryPost]
  | Ok arg =>
      obtain ⟨rcheck, hcheck, hcheckpost⟩ := WP.spec_imp_exists
        (code.check_memory_and_alignment.spec env arg operation.naturalAlign)
      cases rcheck with
      | Err e =>
          simp [code.read_store, hr, hcheck, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Body.Scalar.MemoryPost]
      | Ok u =>
          obtain ⟨⟨r', s'⟩, hp, hc', hpos, rest, hv', hlen, hout'⟩ := WP.spec_imp_exists
            (code.pop_with_type.realizes s outer segment operation.ty (by simpa [hv] using hvals)
              (by simpa [Body.Control.base, hc] using hbase))
          dsimp only at hc' hpos hv' hlen hout'
          cases r' with
          | Err e =>
              simp [code.read_store, hr, hcheck, hp, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Body.Scalar.MemoryPost]
          | Ok popped =>
              obtain ⟨⟨r'', s''⟩, hp', hc'', hpos', rest', hv'', hlen', hout''⟩ := WP.spec_imp_exists
                (code.pop_with_type.realizes s' outer rest .I32 hv'
                  (by simpa [Body.Control.base, hc', hc] using hbase))
              dsimp only at hc'' hpos' hv'' hlen' hout''
              cases r'' with
              | Err e =>
                  simp [code.read_store, hr, hcheck, hp, hp', core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Body.Scalar.MemoryPost]
              | Ok popped =>
                  have hfirst : ∀ ts, Body.Stack.Realizes (Body.Control.polymorphic st) rest ts →
                      Body.Stack.Realizes (Body.Control.polymorphic st) segment (ts ++ [Translation.valueType operation.ty]) := by
                    simpa [Body.Control.polymorphic, hc] using hout'.2
                  have hsecond : ∀ ts, Body.Stack.Realizes (Body.Control.polymorphic st) rest' ts →
                      Body.Stack.Realizes (Body.Control.polymorphic st) rest (ts ++ [.I32]) := by
                    simpa [Body.Control.polymorphic, hc', hc, Translation.valueType] using hout''.2
                  have hpop : ∀ ts, Body.Stack.Realizes (Body.Control.polymorphic st) rest' ts →
                      Body.Stack.Realizes (Body.Control.polymorphic st) segment (ts ++ [.I32, Translation.valueType operation.ty]) := by
                    intro ts ht
                    simpa [List.append_assoc] using hfirst _ (hsecond ts ht)
                  obtain ⟨hwf, hop⟩ := hC.memory_operation opcode operation hrow arg hcheckpost.1 hcheckpost.2
                  have htyping := (Body.ResumePrefix.after_pop htyped hpop).finish hC.wf
                    (operation.op arg) [] hwf
                    (by simpa [Body.MemoryMeaning.Operation.inputs, Body.MemoryMeaning.Operation.outputs, hstore,
                      Translation.valueType] using hop)
                  rw [WP.spec_equiv_exists]
                  refine ⟨(.Ok arg, s''), ?_, ?_⟩
                  · simp [code.read_store, hr, hcheck, hp, hp', core.result.Result.Insts.CoreOpsTry.branch]
                  · intro a heq
                    cases heq
                    exact ⟨by simpa [hpos', hpos] using hout, hc''.trans (hc'.trans hc),
                      rest', hv'', by omega, by simpa using htyping⟩

theorem code.read_memory_size.prefix {inputs : List valtype} (st : code.OpIterState) (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment) (hsize : st.vals.val.length < Usize.max)
    (C : context) (hC : Translation.Environment.Matches env ctx C) (ops : List instr)
    (htyped : Body.TypedPrefix C inputs ops (Body.Control.polymorphic st) segment) :
    code.read_memory_size st data env ⦃ Body.Scalar.ReservedPost inputs data st outer segment C ops .MEMORY_SIZE ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hout⟩ := WP.spec_imp_exists (code.read_reserved_zero.spec st data)
  dsimp only at hv hc hout
  cases r with
  | Err e =>
      simp [code.read_memory_size, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Body.Scalar.ReservedPost]
  | Ok u =>
      obtain ⟨rmem, hmem, hmempost⟩ := WP.spec_imp_exists (code.require_memory.spec env)
      cases rmem with
      | Err e =>
          simp [code.read_memory_size, hr, hmem, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Body.Scalar.ReservedPost]
      | Ok u =>
          obtain ⟨s', hp, hv', hc', hpos⟩ := WP.spec_imp_exists
            (code.push_val.spec s (.Val .I32) (by simpa [hv] using hsize))
          have htyping := (Body.ResumePrefix.of_prefix htyped).finish hC.wf .MEMORY_SIZE [.I32]
            .instr_case_62 (hC.memory_size hmempost)
          rw [WP.spec_equiv_exists]
          refine ⟨(.Ok (), s'), ?_, ?_⟩
          · simp [code.read_memory_size, hr, hmem, hp, core.result.Result.Insts.CoreOpsTry.branch]
          · intro _
            refine ⟨?_, hc'.trans hc, segment ++ [.Val .I32], ?_, by simp, by simpa using htyping⟩
            · simpa [hpos] using hout
            · simpa [hv, hvals, List.append_assoc] using hv'

theorem code.read_memory_grow.prefix {inputs : List valtype} (st : code.OpIterState) (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment) (hbase : (Body.Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (C : context) (hC : Translation.Environment.Matches env ctx C) (ops : List instr)
    (htyped : Body.TypedPrefix C inputs ops (Body.Control.polymorphic st) segment) :
    code.read_memory_grow st data env ⦃ Body.Scalar.ReservedPost inputs data st outer segment C ops .MEMORY_GROW ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hout⟩ := WP.spec_imp_exists (code.read_reserved_zero.spec st data)
  dsimp only at hv hc hout
  cases r with
  | Err e =>
      simp [code.read_memory_grow, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Body.Scalar.ReservedPost]
  | Ok u =>
      obtain ⟨rmem, hmem, hmempost⟩ := WP.spec_imp_exists (code.require_memory.spec env)
      cases rmem with
      | Err e =>
          simp [code.read_memory_grow, hr, hmem, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Body.Scalar.ReservedPost]
      | Ok u =>
          obtain ⟨⟨r', s'⟩, hp, hc', hpos, rest, hv', hlen, hout'⟩ := WP.spec_imp_exists
            (code.pop_with_type.realizes s outer segment .I32 (by simpa [hv] using hvals)
              (by simpa [Body.Control.base, hc] using hbase))
          dsimp only at hc' hpos hv' hlen hout'
          cases r' with
          | Err e =>
              simp [code.read_memory_grow, hr, hmem, hp, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Body.Scalar.ReservedPost]
          | Ok popped =>
              have hcap : s'.vals.val.length < Usize.max := by
                simp only [hv', hvals, List.length_append] at *
                omega
              obtain ⟨s'', hpush, hv'', hc'', hpos'⟩ := WP.spec_imp_exists
                (code.push_val.spec s' (.Val .I32) hcap)
              have hpop : ∀ ts, Body.Stack.Realizes (Body.Control.polymorphic st) rest ts →
                  Body.Stack.Realizes (Body.Control.polymorphic st) segment (ts ++ [.I32]) := by
                simpa [Body.Control.polymorphic, hc, Translation.valueType] using hout'.2
              have htyping := (Body.ResumePrefix.after_pop htyped hpop).finish hC.wf .MEMORY_GROW [.I32]
                .instr_case_63 (hC.memory_grow hmempost)
              rw [WP.spec_equiv_exists]
              refine ⟨(.Ok (), s''), ?_, ?_⟩
              · simp [code.read_memory_grow, hr, hmem, hp, hpush, core.result.Result.Insts.CoreOpsTry.branch]
              · intro _
                exact ⟨by simpa [hpos', hpos] using hout, hc''.trans (hc'.trans hc), rest ++ [.Val .I32],
                  by simpa [hv', List.append_assoc] using hv'', by simpa using Nat.add_le_add_right hlen 1,
                  by simpa using htyping⟩

end Itasca

end

/-! ## MemoryReader -/

section

/-!
Shared scalar load/store source-prefix construction from exact memory-reader facts.
Both validator preservation and compiler inversion retain the same decoded memarg,
byte encoding, and typed operand effect.
-/
namespace Itasca.Body
open Aeneas Aeneas.Std Itasca

theorem Pending.memory_reader_post {data env locals index st}
    (p : Pending data env locals index st) (C : context) (outer : List code.StackType)
    (spine : Frames.Spine env (bodyContext env locals p.ft) p.parents C outer p.current.form p.current.ins)
    (header : Frames.Header env C p.current) (base : p.current.ctrl.value_stack_base.val = outer.length)
    (ctrls : st.core.ctrls.val = p.parents.map Frames.Saved.ctrl ++ [p.current.ctrl])
    (blocks : st.blocks.val = p.parents.map Frames.Saved.bt ++ [p.current.bt])
    (opcode : U8) (operation : Body.MemoryMeaning.Operation)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (meaning : Body.MemoryMeaning.opcodeMeaning opcode = some operation)
    (arg : code.MemArg) (out : code.OpIterState)
    (effect : Itasca.Body.Scalar.MemoryPost ((p.current.form.params p.current.ins).map Translation.valueType)
      data st.core outer p.current.vals (Frames.enter C p.current.form p.current.ins p.current.outs)
      p.current.ops operation.op (.Ok arg, out)) :
    ∃ values, ReaderPost p out (operation.op arg) p.current.ctrl.polymorphic_base values := by
  have poly : Body.Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Body.Control.polymorphic,ctrls]
  obtain ⟨⟨middle,halign,hoffset⟩,controls,rest,stack,length,newTyped⟩ := effect arg rfl
  dsimp only at controls stack hoffset
  have wf := newTyped.wellFormed (operation.op arg) (by simp)
  have encoded1 : Body.Scalar.At data p.start (.plain (operation.op arg)) out.pos := by
    obtain ⟨alignment,ha,hna,hba,hea⟩ := halign
    obtain ⟨offset,ho,hno,hbo,heo⟩ := hoffset
    exact .of_immediate p.inbounds byte p.pos (.memory opcode operation arg meaning hea heo)
      ((show Body.Scalar.BytesAt data st.core.pos alignment middle from ⟨ha,hna,hba⟩).append ⟨ho,hno,hbo⟩)
  have controlEq : out.ctrls.val = p.parents.map Body.Frames.Saved.ctrl ++
      [{p.current.ctrl with polymorphic_base := p.current.ctrl.polymorphic_base}] := by simpa [controls] using ctrls
  have finalTyped := newTyped
  rw [poly] at finalTyped
  have newBlocks : ({st with core := out} : code.BodyState).blocks.val = p.parents.map Body.Frames.Saved.bt ++ [p.current.bt] := by
    simpa [controls,ctrls] using blocks
  refine ⟨rest, ?_⟩
  exact p.append_reader_context C outer spine header base out (operation.op arg)
    p.current.ctrl.polymorphic_base rest wf (.plain encoded1) finalTyped controlEq newBlocks stack
    (encoded1.declared _)

end Itasca.Body

end

end

end

/-! ## Step -/

section

/-!
# Scalar steps

`Pending` preservation for the shared `code.step` arms for non-control opcodes: `nop`,
`unreachable`, `drop`, `select`, constants, locals, globals, memory and numeric instructions.
`Pending.scalar` dispatches on the opcode and shows that a successful scalar step preserves the
typed zipper and appends exactly the independently decoded instruction.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

private theorem Pending.append_scalar {data env locals index st}
    (p : Pending data env locals index st)
    (C : context) (outer : List code.StackType)
    (spine : Frames.Spine env (bodyContext env locals p.ft) p.parents C outer p.current.form p.current.ins)
    (header : Frames.Header env C p.current)
    (base : p.current.ctrl.value_stack_base.val = outer.length)
    (_ctrls : st.core.ctrls.val = p.parents.map Frames.Saved.ctrl ++ [p.current.ctrl])
    (_vals : st.core.vals.val = outer ++ p.current.vals)
    (s : code.OpIterState) (op : instr) (poly : Bool) (newVals : List code.StackType)
    (hwf : wf_instr op) (encoded : Body.Scalar.At data p.start (.plain op) s.pos)
    (typed : TypedPrefix (Frames.enter C p.current.form p.current.ins p.current.outs)
      ((p.current.form.params p.current.ins).map Translation.valueType)
      (p.current.ops ++ [op]) poly newVals)
    (hc : s.ctrls.val = p.parents.map Frames.Saved.ctrl ++
      [{ p.current.ctrl with polymorphic_base := poly }])
    (hv : s.vals.val = outer ++ newVals)
    (_hlen : newVals.length ≤ p.current.vals.length + 1) : p.After {st with core := s} := by
  have hb := p.opened
  obtain ⟨_, _, _, _, _, _, _, blocks, _⟩ := hb
  exact p.append_result C outer spine header base {st with core := s} op poly newVals hwf
    (At.plain encoded) typed hc (by simpa [hc, _ctrls] using blocks) hv
     (encoded.declared _)

end Itasca.Body

namespace Itasca.Body

/-- NOP accepts arbitrary unread suffixes and records its opcode byte. -/
theorem Pending.step_nop {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : Visitor.Total visitor) (v : V)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_NOP) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_NOP v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  apply WP.spec_mono (code.step_nop.total visitor st.core data env ⟨locals, p.ft.results⟩ v hvisitor.to_core)
  intro r hr _
  rw [hr]
  exact (p.nop_reader hbyte).after

/-- UNREACHABLE trims the current frame and records the exact byte. -/
theorem Pending.step_unreachable {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : Visitor.Total visitor) (v : V)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_UNREACHABLE) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_UNREACHABLE v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  refine WP.spec_mono (code.step_unreachable.of_read visitor st.core data env ⟨locals, p.ft.results⟩ v
    (fun _ => True) (fun _ s => p.After {st with core := s}) ?_ hvisitor.to_core) ?_
  · apply WP.spec_mono (p.read_unreachable hbyte)
    intro r effect
    exact ⟨trivial, fun _ _ => effect.2.2.after⟩
  · intro r hr hok
    exact (hr.2 hok).choose_spec

/-- DROP covers concrete and polymorphic operands, and may reject an empty stack. -/
theorem Pending.step_drop {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : Visitor.Total visitor) (v : V)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_DROP) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_DROP v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  refine WP.spec_mono (code.step_drop.of_read visitor st.core data env ⟨locals, p.ft.results⟩ v
    (fun _ => True) (fun _ s => p.After {st with core := s}) ?_ hvisitor.to_core) ?_
  · apply WP.spec_mono (p.read_drop hbyte)
    intro r effect
    refine ⟨trivial, ?_⟩
    intro value accepted
    obtain ⟨_, _, post⟩ := effect value accepted
    exact post.after
  · intro r effect accepted
    exact (effect.2 accepted).choose_spec

end Itasca.Body

namespace Itasca.Body

/-- The i32 constant step terminates on arbitrary immediate bytes and preserves the invariant on success. -/
theorem Pending.step_i32_const {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : Visitor.Total visitor) (v : V) (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_I32_CONST) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_I32_CONST v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  refine WP.spec_mono (code.step_i32_const.of_read visitor st.core data env ⟨locals, p.ft.results⟩ v
    (fun _ => True) (fun _ s => p.After {st with core := s}) ?_ hvisitor.to_core) ?_
  · apply WP.spec_mono (p.read_i32_const hsize hbyte)
    intro r effect
    exact ⟨trivial, fun value accepted => (effect value accepted).2.after⟩
  · intro r hr hok
    exact (hr.2 hok).choose_spec

/-- The i64 constant step terminates on arbitrary immediate bytes and preserves the invariant on success. -/
theorem Pending.step_i64_const {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : Visitor.Total visitor) (v : V) (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_I64_CONST) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_I64_CONST v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  refine WP.spec_mono (code.step_i64_const.of_read visitor st.core data env ⟨locals, p.ft.results⟩ v
    (fun _ => True) (fun _ s => p.After {st with core := s}) ?_ (hvisitor.on_i64_const v)) ?_
  · apply WP.spec_mono (p.read_i64_const hsize hbyte)
    intro r effect
    exact ⟨trivial, fun value accepted => (effect value accepted).2.after⟩
  · intro r hr hok
    exact (hr.2 hok).choose_spec

/-- The f32 constant step terminates on arbitrary immediate bytes and preserves the invariant on success. -/
theorem Pending.step_f32_const {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : Visitor.Total visitor) (v : V) (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_F32_CONST) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_F32_CONST v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  refine WP.spec_mono (code.step_f32_const.of_read visitor st.core data env ⟨locals, p.ft.results⟩ v
    (fun _ => True) (fun _ s => p.After {st with core := s}) ?_ (hvisitor.on_f32_const v)) ?_
  · apply WP.spec_mono (p.read_f32_const hsize hbyte)
    intro r effect
    exact ⟨trivial, fun value accepted => (effect value accepted).2.after⟩
  · intro r hr hok
    exact (hr.2 hok).choose_spec

/-- The f64 constant step terminates on arbitrary immediate bytes and preserves the invariant on success. -/
theorem Pending.step_f64_const {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : Visitor.Total visitor) (v : V) (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_F64_CONST) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_F64_CONST v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  refine WP.spec_mono (code.step_f64_const.of_read visitor st.core data env ⟨locals, p.ft.results⟩ v
    (fun _ => True) (fun _ s => p.After {st with core := s}) ?_ (hvisitor.on_f64_const v)) ?_
  · apply WP.spec_mono (p.read_f64_const hsize hbyte)
    intro r effect
    exact ⟨trivial, fun value accepted => (effect value accepted).2.after⟩
  · intro r hr hok
    exact (hr.2 hok).choose_spec

end Itasca.Body

namespace Itasca.Body

/-- Every numeric opcode extends the generated typing derivation under the current frame context. -/
theorem Pending.step_numeric_mapped {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : Visitor.Total visitor) (v : V) (hsize : st.core.vals.val.length < Usize.max) (opcode : U8) (op : Body.Numeric.Operation)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode)
    (hmap : Body.Numeric.opcodeMeaning opcode = some op) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ opcode v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  have encoded : Body.Scalar.At data p.start (.plain op.instruction) st.core.pos :=
    .no_immediate p.inbounds hbyte p.pos (.numeric opcode op hmap)
  have effect := p.numeric_reader op st.core.pos hsize (.plain encoded) (encoded.declared _)

  dsimp only at effect
  rw [code.step.numeric_dispatch visitor st.core data env ⟨locals,p.ft.results⟩ opcode v (Body.Numeric.NumericOp.bounds hmap).1]
  rw [code.step_numeric.dispatch visitor st.core opcode op v hmap]
  apply WP.spec_mono (Visitor.Core.run.spec _ _ v (fun _ => True)
    (fun _ out => p.After {st with core := out}) ?_ (fun out _ => hvisitor.visit_numeric v out opcode))
  · intro result held accepted
    exact (held.2 accepted).choose_spec
  · apply WP.spec_mono effect
    intro result held
    refine ⟨trivial, ?_⟩
    intro unit accepted
    obtain ⟨_, _, post⟩ := held.2.2 unit accepted
    exact post.after

/-- Unmapped high opcodes terminate with rejection; mapped scalar opcodes preserve the invariant. -/
theorem Pending.step_numeric {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : Visitor.Total visitor) (v : V) (hsize : st.core.vals.val.length < Usize.max) (opcode : U8)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode) (hlow : 0x45 ≤ opcode.val) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ opcode v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  cases hm : Body.Numeric.opcodeMeaning opcode with
  | none =>
    rw [code.step.numeric_dispatch visitor st.core data env ⟨locals, p.ft.results⟩ opcode v hlow,
      code.step_numeric.unrecognized visitor st.core opcode v hm]
    simp
  | some op => exact p.step_numeric_mapped visitor hvisitor v hsize opcode op hbyte hm

/-- SELECT preserves its joined concrete/bottom result and exact opcode provenance. -/
theorem Pending.step_select {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : Visitor.Total visitor) (v : V) (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_SELECT) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_SELECT v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  rw [code.step_select.dispatch]
  refine WP.spec_mono (Visitor.Core.run.spec _ _ v (fun _ => True)
    (fun _ s => p.After {st with core := s}) ?_ (hvisitor.on_select v)) ?_
  · apply WP.spec_mono (p.read_select hsize hbyte)
    intro r effect
    refine ⟨trivial, ?_⟩
    intro value accepted
    obtain ⟨_, _, post⟩ := effect value accepted
    exact post.after
  · intro r effect accepted
    exact (effect.2 accepted).choose_spec

end Itasca.Body

namespace Itasca.Body

private theorem run_after {A V : Type} {data env locals index st}
    (p : Pending data env locals index st)
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (v : V) (hread : read ⦃ r => ∀ a, r.1 = .Ok a → p.After {st with core := r.2} ⦄)
    (hhook : ∀ s a, ∃ res v', hook v s a = .ok (res, v')) :
    Visitor.Core.run read hook v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  refine WP.spec_mono (Visitor.Core.run.spec read hook v (fun _ => True) (fun _ s => p.After {st with core := s})
    (WP.spec_mono hread (fun _ h => ⟨trivial, h⟩)) hhook) ?_
  intro r h hr
  obtain ⟨_, ha⟩ := h.2 hr
  exact ha

private theorem Pending.index_post_after {data env locals index st} (p : Pending data env locals index st)
    (C : context) (outer : List code.StackType)
    (spine : Frames.Spine env (bodyContext env locals p.ft) p.parents C outer p.current.form p.current.ins)
    (header : Frames.Header env C p.current)
    (base : p.current.ctrl.value_stack_base.val = outer.length)
    (ctrls : st.core.ctrls.val = p.parents.map Frames.Saved.ctrl ++ [p.current.ctrl])
    (vals : st.core.vals.val = outer ++ p.current.vals)
    (opcode : U8) (op : U32 → instr) (hbyte : data.val[p.start.val]'p.inbounds = opcode)
    (hwf : ∀ idx, wf_instr (op idx))
    (himm : ∀ idx bytes, Binary.Leb128.Encoding bytes idx.val → Body.Scalar.Immediate opcode (.plain (op idx)) bytes)
    (r : core.result.Result U32 error.OpError × code.OpIterState)
    (hpost : Itasca.Body.Scalar.IndexPost ((p.current.form.params p.current.ins).map Translation.valueType) data st.core outer p.current.vals
      (Frames.enter C p.current.form p.current.ins p.current.outs) p.current.ops op r)
    (idx : U32) (hr : r.1 = .Ok idx) :
    p.After {st with core := r.2} := by
  rcases r with ⟨result, out⟩
  dsimp only at hr
  subst result
  obtain ⟨_, _, _, _, _, _, _, blocks, _⟩ := p.opened
  obtain ⟨values, _, post⟩ := p.index_reader_post C outer spine header base ctrls blocks
    opcode op hbyte hwf himm out idx hpost
  exact post.after

/-- `local.get` preserves `Pending` on success. -/
theorem Pending.step_local_get {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hsize : st.core.vals.val.length < Usize.max) (hvisitor : Visitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x20#u8) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_LOCAL_GET v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hpoly : Body.Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Body.Control.polymorphic, ctrls]
  have hC : Translation.Environment.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (Translation.Environment.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  rw [code.step_local_get.dispatch]
  apply run_after p _ _ v _ (hvisitor.on_local_get v)
  refine WP.spec_mono (code.read_local_get.prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    hsize _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr idx hi
  exact p.index_post_after C outer spine header base ctrls vals 0x20#u8 _ hbyte
    (fun idx => .instr_case_43 _ (Translation.Environment.index_wf idx))
    (fun idx _ he => .localGet idx he) r hr idx hi

/-- `local.set` preserves `Pending` on success. -/
theorem Pending.step_local_set {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hvisitor : Visitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x21#u8) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_LOCAL_SET v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hpoly : Body.Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Body.Control.polymorphic, ctrls]
  have hC : Translation.Environment.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (Translation.Environment.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  rw [code.step_local_set.dispatch]
  apply run_after p _ _ v _ (hvisitor.on_local_set v)
  refine WP.spec_mono (code.read_local_set.prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    (by simpa [Body.Control.base, ctrls] using base) _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr idx hi
  exact p.index_post_after C outer spine header base ctrls vals 0x21#u8 _ hbyte
    (fun idx => .instr_case_44 _ (Translation.Environment.index_wf idx))
    (fun idx _ he => .localSet idx he) r hr idx hi

/-- `local.tee` preserves `Pending` on success. -/
theorem Pending.step_local_tee {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hsize : st.core.vals.val.length < Usize.max) (hvisitor : Visitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x22#u8) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_LOCAL_TEE v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hpoly : Body.Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Body.Control.polymorphic, ctrls]
  have hC : Translation.Environment.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (Translation.Environment.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  rw [code.step_local_tee.dispatch]
  apply run_after p _ _ v _ (hvisitor.on_local_tee v)
  refine WP.spec_mono (code.read_local_tee.prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    (by simpa [Body.Control.base, ctrls] using base)
    hsize _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr idx hi
  exact p.index_post_after C outer spine header base ctrls vals 0x22#u8 _ hbyte
    (fun idx => .instr_case_45 _ (Translation.Environment.index_wf idx))
    (fun idx _ he => .localTee idx he) r hr idx hi

/-- `global.get` preserves `Pending` on success. -/
theorem Pending.step_global_get {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hsize : st.core.vals.val.length < Usize.max) (hvisitor : Visitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x23#u8) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_GLOBAL_GET v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hpoly : Body.Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Body.Control.polymorphic, ctrls]
  have hC : Translation.Environment.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (Translation.Environment.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  rw [code.step_global_get.dispatch]
  apply run_after p _ _ v _ (hvisitor.on_global_get v)
  refine WP.spec_mono (code.read_global_get.prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    hsize _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr idx hi
  exact p.index_post_after C outer spine header base ctrls vals 0x23#u8 _ hbyte
    (fun idx => .instr_case_46 _ (Translation.Environment.index_wf idx))
    (fun idx _ he => .globalGet idx he) r hr idx hi

/-- `global.set` preserves `Pending` on success. -/
theorem Pending.step_global_set {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hvisitor : Visitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x24#u8) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_GLOBAL_SET v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hpoly : Body.Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Body.Control.polymorphic, ctrls]
  have hC : Translation.Environment.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (Translation.Environment.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  rw [code.step_global_set.dispatch]
  apply run_after p _ _ v _ (hvisitor.on_global_set v)
  refine WP.spec_mono (code.read_global_set.prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    (by simpa [Body.Control.base, ctrls] using base) _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr idx hi
  exact p.index_post_after C outer spine header base ctrls vals 0x24#u8 _ hbyte
    (fun idx => .instr_case_47 _ (Translation.Environment.index_wf idx))
    (fun idx _ he => .globalSet idx he) r hr idx hi

private theorem Pending.reserved_post_after {data env locals index st} (p : Pending data env locals index st)
    (C : context) (outer : List code.StackType)
    (spine : Frames.Spine env (bodyContext env locals p.ft) p.parents C outer p.current.form p.current.ins)
    (header : Frames.Header env C p.current)
    (base : p.current.ctrl.value_stack_base.val = outer.length)
    (ctrls : st.core.ctrls.val = p.parents.map Frames.Saved.ctrl ++ [p.current.ctrl])
    (vals : st.core.vals.val = outer ++ p.current.vals)
    (opcode : U8) (op : instr) (hbyte : data.val[p.start.val]'p.inbounds = opcode)
    (hwf : wf_instr op) (himm : Body.Scalar.Immediate opcode (.plain op) [0#u8])
    (r : core.result.Result Unit error.OpError × code.OpIterState)
    (hpost : Itasca.Body.Scalar.ReservedPost ((p.current.form.params p.current.ins).map Translation.valueType) data st.core outer p.current.vals
      (Frames.enter C p.current.form p.current.ins p.current.outs) p.current.ops op r)
    (hr : r.1 = .Ok ()) :
    p.After {st with core := r.2} := by
  obtain ⟨⟨hp, hz, hn⟩, hc, rest, hv, hl, ht⟩ := hpost hr
  have hpoly : Body.Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Body.Control.polymorphic, ctrls]
  apply p.append_scalar C outer spine header base ctrls vals r.2 op
    p.current.ctrl.polymorphic_base rest hwf _ (by simpa [hpoly] using ht) _ hv hl
  · exact .of_immediate p.inbounds hbyte p.pos himm (.byte data st.core.pos r.2.pos 0#u8 hp hz hn)
  · simp [hc, ctrls]

/-- `memory.size` preserves `Pending` on success. -/
theorem Pending.step_memory_size {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hsize : st.core.vals.val.length < Usize.max) (hvisitor : Visitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x3F#u8) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_MEMORY_SIZE v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hpoly : Body.Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Body.Control.polymorphic, ctrls]
  have hC : Translation.Environment.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (Translation.Environment.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  rw [code.step_memory_size.dispatch]
  apply run_after p _ _ v _ (fun s _ => hvisitor.on_memory_size v s)
  refine WP.spec_mono (code.read_memory_size.prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    hsize _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr u hi
  cases u
  exact p.reserved_post_after C outer spine header base ctrls vals 0x3F#u8 _ hbyte
    .instr_case_62 .memorySize r hr hi

/-- `memory.grow` preserves `Pending` on success. -/
theorem Pending.step_memory_grow {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hsize : st.core.vals.val.length < Usize.max) (hvisitor : Visitor.Total visitor)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x40#u8) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_MEMORY_GROW v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hpoly : Body.Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Body.Control.polymorphic, ctrls]
  have hC : Translation.Environment.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (Translation.Environment.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  rw [code.step_memory_grow.dispatch]
  apply run_after p _ _ v _ (fun s _ => hvisitor.on_memory_grow v s)
  refine WP.spec_mono (code.read_memory_grow.prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    (by simpa [Body.Control.base, ctrls] using base) hsize
    _ hC p.current.ops (by simpa [hpoly] using typed)) ?_
  intro r hr u hi
  cases u
  exact p.reserved_post_after C outer spine header base ctrls vals 0x40#u8 _ hbyte
    .instr_case_63 .memoryGrow r hr hi

/-- Loads and stores preserve `Pending` on success. -/
theorem Pending.step_memory {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hsize : st.core.vals.val.length < Usize.max) (hvisitor : Visitor.Total visitor)
    (opcode : U8) (operation : Body.MemoryMeaning.Operation)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode)
    (hrow : Body.MemoryMeaning.opcodeMeaning opcode = some operation) :
    code.step visitor st.core data env ⟨locals, p.ft.results⟩ opcode v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hpoly : Body.Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Body.Control.polymorphic, ctrls]
  have hC : Translation.Environment.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (Translation.Environment.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  have hb : (Body.Control.base st.core).val = outer.length := by simpa [Body.Control.base, ctrls] using base
  have hread : (if operation.store then code.read_store st.core data env operation.ty operation.naturalAlign
      else code.read_load st.core data env operation.ty operation.naturalAlign) ⦃
        Itasca.Body.Scalar.MemoryPost ((p.current.form.params p.current.ins).map Translation.valueType) data st.core outer p.current.vals
          (Frames.enter C p.current.form p.current.ins p.current.outs) p.current.ops operation.op ⦄ := by
    cases hs : operation.store with
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact code.read_load.prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals hb
          hsize _ hC p.current.ops (by simpa [hpoly] using typed)
          opcode operation hrow hs
    | true =>
        simp only [↓reduceIte]
        exact code.read_store.prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals hb
          _ hC p.current.ops (by simpa [hpoly] using typed) opcode operation hrow hs
  rw [code.step_memory.dispatch visitor st.core data env ⟨locals, p.ft.results⟩ v opcode operation hrow]
  apply run_after p _ _ v _ (fun s arg => hvisitor.visit_memory v s opcode arg)
  refine WP.spec_mono hread ?_
  intro r hr arg hi
  rcases r with ⟨result, out⟩
  dsimp only at hi
  subst result
  obtain ⟨values, post⟩ := p.memory_reader_post C outer spine header base ctrls blocks
    opcode operation hbyte hrow arg out hr
  exact post.after

end Itasca.Body
namespace Itasca.Body

/-- Successful shared scalar dispatch preserves the control zipper
and appends exactly the independently decoded instruction. -/
theorem Pending.scalar {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hvisitor : Visitor.Total visitor)
    (ctx : code.Context) (hlocals : ctx.locals = locals)
    (opcode : U8) (hscalar : opcode.val ∉ controlOpcodes)
    (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode) :
    code.step visitor st.core data env ctx opcode v ⦃ r =>
      r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  rw [scalar_context visitor st.core data env ctx ⟨locals, p.ft.results⟩ opcode v hscalar hlocals]
  by_cases hhigh : 0x45 ≤ opcode.val
  · exact p.step_numeric visitor hvisitor v hsize opcode hbyte hhigh
  by_cases hmemory : 0x28 ≤ opcode.val ∧ opcode.val ≤ 0x3E
  · obtain ⟨operation, hm⟩ := memory_meaning_exists opcode hmemory.1 hmemory.2
    exact p.step_memory visitor v hsize hvisitor opcode operation hbyte hm
  by_cases h_nop : opcode = code.OP_NOP
  · rw [h_nop] at hbyte ⊢; exact p.step_nop visitor hvisitor v hbyte
  by_cases h_unreachable : opcode = code.OP_UNREACHABLE
  · rw [h_unreachable] at hbyte ⊢; exact p.step_unreachable visitor hvisitor v hbyte
  by_cases h_i32_const : opcode = code.OP_I32_CONST
  · rw [h_i32_const] at hbyte ⊢; exact p.step_i32_const visitor hvisitor v hsize hbyte
  by_cases h_i64_const : opcode = code.OP_I64_CONST
  · rw [h_i64_const] at hbyte ⊢; exact p.step_i64_const visitor hvisitor v hsize hbyte
  by_cases h_f32_const : opcode = code.OP_F32_CONST
  · rw [h_f32_const] at hbyte ⊢; exact p.step_f32_const visitor hvisitor v hsize hbyte
  by_cases h_f64_const : opcode = code.OP_F64_CONST
  · rw [h_f64_const] at hbyte ⊢; exact p.step_f64_const visitor hvisitor v hsize hbyte
  by_cases h_drop : opcode = code.OP_DROP
  · rw [h_drop] at hbyte ⊢; exact p.step_drop visitor hvisitor v hbyte
  by_cases h_select : opcode = code.OP_SELECT
  · rw [h_select] at hbyte ⊢; exact p.step_select visitor hvisitor v hsize hbyte
  by_cases h_local_get : opcode = code.OP_LOCAL_GET
  · rw [h_local_get] at hbyte ⊢; exact p.step_local_get visitor v hsize hvisitor (by simpa [global_simps] using hbyte)
  by_cases h_local_set : opcode = code.OP_LOCAL_SET
  · rw [h_local_set] at hbyte ⊢; exact p.step_local_set visitor v hvisitor (by simpa [global_simps] using hbyte)
  by_cases h_local_tee : opcode = code.OP_LOCAL_TEE
  · rw [h_local_tee] at hbyte ⊢; exact p.step_local_tee visitor v hsize hvisitor (by simpa [global_simps] using hbyte)
  by_cases h_global_get : opcode = code.OP_GLOBAL_GET
  · rw [h_global_get] at hbyte ⊢; exact p.step_global_get visitor v hsize hvisitor (by simpa [global_simps] using hbyte)
  by_cases h_global_set : opcode = code.OP_GLOBAL_SET
  · rw [h_global_set] at hbyte ⊢; exact p.step_global_set visitor v hvisitor (by simpa [global_simps] using hbyte)
  by_cases h_memory_size : opcode = code.OP_MEMORY_SIZE
  · rw [h_memory_size] at hbyte ⊢; exact p.step_memory_size visitor v hsize hvisitor (by simpa [global_simps] using hbyte)
  by_cases h_memory_grow : opcode = code.OP_MEMORY_GROW
  · rw [h_memory_grow] at hbyte ⊢; exact p.step_memory_grow visitor v hsize hvisitor (by simpa [global_simps] using hbyte)
  have hreserved : (0x06 ≤ opcode.val ∧ opcode.val ≤ 0x0A) ∨
      (0x12 ≤ opcode.val ∧ opcode.val ≤ 0x19) ∨
      (0x1C ≤ opcode.val ∧ opcode.val ≤ 0x1F) ∨
      (0x25 ≤ opcode.val ∧ opcode.val ≤ 0x27) := by
    simp only [controlOpcodes, List.mem_cons, not_or] at hscalar
    simp only [global_simps] at *
    scalar_tac
  rw [code.step.reserved visitor st.core data env ⟨locals, p.ft.results⟩ opcode v hreserved]
  simp

end Itasca.Body

end
