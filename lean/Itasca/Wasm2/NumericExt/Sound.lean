import Itasca.Wasm2.Step.Context
import Itasca.Wasm2.Complete.Frame
import Itasca.Wasm2.NumericExt.Total
import Itasca.Handler.RawControl
import Itasca.Wasm2.Scalar.NumericReader
import Itasca.Wasm2.Scalar.Step

/-!
Sections, each formerly its own module: Complete, Sound.
-/

/-! ## Complete -/

section

/-!
# Numeric extension completeness

Acceptance of the sign-extension and saturating truncation opcodes by `code.step_extended` from
independent premises. `Frame.sign_extension` and `Frame.saturating` give the two arms, and
`base_immediate` and `wasm2_base_immediate` show which Wasm 1.0 opcodes stay with the shared
dispatcher.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Completeness

private theorem empty_sign (st : code.OpIterState) (opcode : U8) :
    code.visit_sign_extension code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor () st opcode =
      .ok (.Ok (), ()) := by
  unfold code.visit_sign_extension
  split <;> rfl

private theorem empty_saturating (st : code.OpIterState) (opcode : U32) :
    code.visit_saturating code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor () st opcode =
      .ok (.Ok (), ()) := by
  unfold code.visit_saturating
  split <;> rfl

/-- A sign-extension byte accepts its independently typed principal effect. -/
theorem Frame.sign_extension {st} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (opcode : U8) (op : Numeric.Operation) (next : Usize)
    (C : context) (front ins outs : List valtype)
    (hmap : NumericExtensions.signMeaning opcode = some op)
    (hb : Wasm1.BytesAt data st.core.pos [] next)
    (hsize : st.core.vals.val.length < Usize.max)
    (ht : Instr_ok C op.instruction (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ ins)) :
    ∃ s, step st data env ctx index opcode = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ outs) s ∧ s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  obtain ⟨rfl, rfl⟩ := NumericExtensions.sign_signature hmap C ins outs ht
  obtain ⟨s, after, hs, hc, hp, hv, hl, hout⟩ := Numeric.read.complete op st.core f.core.outer
    f.core.operands front f.core.vals f.core.base_eq hsize (by simpa [f.core.poly_eq] using hr)
  have props := NumericExtensions.sign_properties hmap
  simp only [Numeric.read, props.1, Bool.false_eq_true, ↓reduceIte] at hs
  have hscalar : opcode.val ∉ controlOpcodes := by
    simp only [controlOpcodes, List.mem_cons, List.not_mem_nil, or_false, not_or]
    omega
  refine ⟨{st with core := s}, ?_, hp.trans hb.empty.symm,
    ⟨f.core.output_of_same_ctrls hc hv hout, code.BodyState.blocks_eq_of_ctrls hc⟩, ?_⟩
  · rw [step.scalar_eq st data env ctx index opcode hscalar]
    have hn : alloc.vec.Vec.len st.core.vals ≠ core.num.Usize.MAX := by scalar_tac
    rw [if_neg hn, code.step_wasm2.base _ _ _ _ _ _ _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      omega), code.step_extended.sign _ _ _ _ _ _ _ _ hmap]
    simp [CoreVisitor.run, hs, empty_sign, code.visit, core.result.Result.Insts.CoreOpsTry.branch]
  · simp only [hv, f.core.vals, List.length_append]
    omega

/-- A saturating conversion accepts every valid u32 LEB encoding of its subopcode. -/
theorem Frame.saturating {st} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (subopcode : U32) (op : Numeric.Operation)
    (bytes : List U8) (next : Usize) (C : context) (front ins outs : List valtype)
    (hmap : NumericExtensions.saturatingMeaning subopcode = some op)
    (he : Leb128.Encoding bytes subopcode.val) (hb : Wasm1.BytesAt data st.core.pos bytes next)
    (hsize : st.core.vals.val.length < Usize.max)
    (ht : Instr_ok C op.instruction (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ ins)) :
    ∃ s, step st data env ctx index 0xFC#u8 = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ outs) s ∧ s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  obtain ⟨rfl, rfl⟩ := NumericExtensions.saturating_signature hmap C ins outs ht
  let decoded : code.OpIterState := {st.core with pos := next}
  obtain ⟨s, after, hs, hc, hp, hv, hl, hout⟩ := Numeric.read.complete op decoded f.core.outer
    f.core.operands front f.core.vals f.core.base_eq hsize (by simpa only [decoded, Control.polymorphic, f.core.ctrls, List.getLast?_concat] using hr)
  simp only [Numeric.read, NumericExtensions.saturating_unary hmap, Bool.false_eq_true, ↓reduceIte] at hs
  have hread := hb.read_u32 subopcode he
  refine ⟨{st with core := s}, ?_, hp,
    ⟨f.core.output_of_same_ctrls hc hv hout, code.BodyState.blocks_eq_of_ctrls hc⟩, ?_⟩
  · rw [step.scalar_eq st data env ctx index 0xFC#u8 (by decide)]
    have hn : alloc.vec.Vec.len st.core.vals ≠ core.num.Usize.MAX := by scalar_tac
    have hd : Leb128.Decoded data st.core.pos subopcode next := ⟨bytes, hb.suffix, hb.length, hb.bound, he⟩
    have hsub : subopcode.val < 8 := by
      unfold NumericExtensions.saturatingMeaning at hmap
      split at hmap <;> simp_all
    rw [if_neg hn, code.step_wasm2.saturating _ _ _ _ _ _ _ _ hd hsub,
      code.step_extended.prefixed]
    simp [prefixedStep, hread, hmap, CoreVisitor.run, hs, decoded, empty_saturating,
      code.visit, core.result.Result.Insts.CoreOpsTry.branch]
  · simp only [hv, f.core.vals, List.length_append]
    omega

end Itasca.Wasm2.Completeness

namespace Itasca.Wasm2

/-- The Wasm 1.0 leaf grammar never enters a sign-extension or `0xfc` prefix arm. -/
theorem base_immediate {opcode op bytes} (hi : Wasm1.Immediate opcode (.plain op) bytes) :
    NumericExtensions.signMeaning opcode = none ∧ opcode ≠ code.OP_MISC_PREFIX := by
  have hb : opcode.val < 192 := by
    cases hi with
    | numeric opcode operation hmap =>
      have := Numeric.NumericOp.bounds hmap
      omega
    | memory opcode operation arg hmap ha ho =>
      unfold MemoryMeaning.opcodeMeaning at hmap
      split at hmap <;> simp_all
    | _ => decide
  constructor
  · unfold NumericExtensions.signMeaning
    split <;> simp_all
  · intro he
    have := congrArg UScalar.val he
    simp only [code.OP_MISC_PREFIX] at this
    change opcode.val = 252 at this
    omega

/-- The Wasm 1.0 leaf grammar never selects a reference, table, or vector arm of `code.step_wasm2`
(opcodes `0x1c`, `0x25`, `0x26`, `0xd0` to `0xd2`, `0xfc`, `0xfd`). -/
theorem wasm2_base_immediate {opcode op bytes} (hi : Wasm1.Immediate opcode (.plain op) bytes) :
    opcode.val ∉ [28, 37, 38, 208, 209, 210, 252, 253] := by
  cases hi with
  | numeric opcode operation hmap =>
    have := Numeric.NumericOp.bounds hmap
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    omega
  | memory opcode operation arg hmap ha ho =>
    unfold MemoryMeaning.opcodeMeaning at hmap
    split at hmap <;> simp_all
  | _ => decide

end Itasca.Wasm2

end

/-! ## Sound -/

section

/-!
# Numeric extension steps

`Pending` preservation for `code.step_extended`. `Pending.extended_numeric` handles a unary
numeric extension, and `Pending.extended_scalar` combines the sign-extension, saturating and
shared-scalar arms into one successful-step certificate.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- A unary numeric extension preserves the control zipper while recording
its independently encoded instruction, including any consumed prefix bytes. -/
theorem Pending.extended_numeric {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (v : V)
    (operation : Numeric.Operation) (hunary : operation.binary = false)
    (hdecl : DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) operation.instruction)
    (pos : Usize) (hsize : st.core.vals.val.length < Usize.max)
    (hook : V → code.OpIterState → Unit → Result (core.result.Result Unit error.VisitError × V))
    (hhook : ∀ s a, ∃ reply v', hook v s a = .ok (reply, v'))
    (hencoded : At data p.start (.plain operation.instruction) pos) :
    CoreVisitor.run (code.read_conversion {st.core with pos := pos} operation.input operation.output)
      hook v ⦃ r => r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  have effect := p.numeric_reader operation pos hsize hencoded hdecl

  simp only [Numeric.read, hunary, Bool.false_eq_true, ↓reduceIte] at effect
  apply WP.spec_mono (CoreVisitor.run.spec _ hook v (fun _ => True)
    (fun _ s => p.After {st with core := s}) ?_ hhook)
  · intro r hr accepted
    exact (hr.2 accepted).choose_spec
  · apply WP.spec_mono effect
    intro r hr
    refine ⟨trivial, ?_⟩
    intro unit accepted
    obtain ⟨_, _, post⟩ := hr.2.2 unit accepted
    exact post.after

/-- Scalar extensions and the base dispatcher share the same successful-step certificate. -/
theorem Pending.extended_scalar {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hv : FullVisitor.Total visitor)
    (ctx : code.Context) (hlocals : ctx.locals = locals)
    (opcode : U8) (hscalar : opcode.val ∉ controlOpcodes)
    (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode) :
    code.step_extended visitor st.core data env ctx opcode v ⦃ r =>
      r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  cases hm : NumericExtensions.signMeaning opcode with
  | some operation =>
    rw [code.step_extended.sign visitor st.core data env ctx opcode operation v hm]
    apply p.extended_numeric v
      operation (NumericExtensions.sign_properties hm).1 (NumericExtensions.sign_declared hm _) st.core.pos hsize
      _ (fun s _ => hv.visit_sign_extension v s opcode)
    exact At.of_immediate p.inbounds hbyte p.pos (.signExtension opcode operation hm)
      (Wasm1.BytesAt.nil data st.core.pos (by have := p.pos; have := p.inbounds; omega))
  | none =>
    by_cases hprefix : opcode = code.OP_MISC_PREFIX
    · have he : opcode = 0xFC#u8 := by simpa [global_simps] using hprefix
      rw [he] at hbyte ⊢
      rw [code.step_extended.prefixed]
      obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
      unfold prefixedStep
      rw [hr]
      simp only [bind_ok]
      cases r with
      | Err e => simp
      | Ok pair =>
        obtain ⟨subopcode, next⟩ := pair
        cases hm : NumericExtensions.saturatingMeaning subopcode with
        | none => simp [hm]
        | some operation =>
          simp only [hm]
          apply p.extended_numeric v
            operation (NumericExtensions.saturating_unary hm) (NumericExtensions.saturating_declared hm _) next hsize
            _ (fun s _ => hv.visit_saturating v s subopcode)
          obtain ⟨bytes, hs, hn, hb, he⟩ := hd
          exact At.of_immediate p.inbounds hbyte p.pos (.saturating subopcode operation hm he)
            ⟨hs, hn, hb⟩
    · rw [code.step_extended.base visitor st.core data env ctx opcode v hm hprefix]
      exact p.scalar visitor v hv ctx hlocals opcode hscalar hsize hbyte

end Itasca.Wasm2

end
