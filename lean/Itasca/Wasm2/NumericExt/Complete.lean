import Itasca.Wasm2.Step.Context
import Itasca.Wasm2.Complete.Frame
import Itasca.Wasm2.NumericExt.Total
import Itasca.Handler.ScalarComplete

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
theorem Frame.sign_extension {st} (f : Frame st) (data : Slice U8) (env : module.Env)
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
theorem Frame.saturating {st} (f : Frame st) (data : Slice U8) (env : module.Env)
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
      split at hmap <;> simp_all <;> omega
    rw [if_neg hn, code.step_wasm2.saturating _ _ _ _ _ _ _ _ hd hsub,
      code.step_extended.prefixed]
    simp [prefixedStep, hread, hmap, CoreVisitor.run, hs, decoded, empty_saturating,
      code.visit, core.result.Result.Insts.CoreOpsTry.branch]
  · simp only [hv, f.core.vals, List.length_append]
    omega

end Itasca.Wasm2.Completeness

namespace Itasca.Wasm2

/-- The inherited Wasm 1.0 leaf grammar never enters an extension dispatch arm. -/
theorem base_immediate {opcode op bytes} (hi : Wasm1.Immediate opcode (.plain op) bytes) :
    NumericExtensions.signMeaning opcode = none ∧ opcode ≠ code.OP_MISC_PREFIX := by
  have hb : opcode.val < 192 := by
    cases hi with
    | numeric opcode operation hmap =>
      have := Numeric.NumericOp.bounds hmap
      omega
    | memory opcode operation arg hmap ha ho =>
      unfold MemoryMeaning.opcodeMeaning at hmap
      split at hmap <;> simp_all <;> omega
    | _ => decide
  constructor
  · unfold NumericExtensions.signMeaning
    split <;> simp_all <;> omega
  · intro he
    have := congrArg UScalar.val he
    simp only [code.OP_MISC_PREFIX] at this
    change opcode.val = 252 at this
    omega

/-- The inherited grammar never selects the new reference, table, or vector arms. -/
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
