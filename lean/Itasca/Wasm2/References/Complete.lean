import Itasca.Wasm2.References.ReadersComplete
import Itasca.Wasm2.Complete.Frame
import Itasca.Wasm2.Step.Context
import Itasca.Wasm2.Step.Dispatch
import Itasca.Wasm2.Bulk.Dispatch

/-!
# Completeness of reference and table instructions

For each reference and table instruction handled by `code.step_wasm2` (`ref.null`, `ref.is_null`,
`ref.func`, `table.get`, `table.set`, `table.grow`, `table.size`, `table.fill` and typed
`select`), the `Completeness.Frame.*` lemmas show that `Wasm2.step` accepts the independent
encoding at a realized operand stack and produces the expected output. Wasm 2.0 only.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Completeness

/-- Complete metadata decoding followed by the shared fixed operand checker.
The contract fixes the final cursor and keeps the original control frames. -/
theorem Frame.metadata_read {st} (f : Frame st) {A B : Type}
    (decode : Result (core.result.Result A error.OpError × code.OpIterState))
    (a : A) (next : Usize) (pops : A → List wasm_types.ValueType)
    (output : A → Option wasm_types.ValueType) (metadata : A → B) (front : List valtype)
    (hd : decode = .ok (.Ok a, {st.core with pos := next}))
    (hsize : st.core.vals.val.length < Usize.max)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands
      (front ++ Simd.inputTypes (pops a))) :
    ∃ s, metadataOperands decode pops output metadata = .ok (.Ok (metadata a), s) ∧
      s.pos = next ∧ f.Output (front ++ Simd.outputTypes (output a)) {st with core := s} ∧
      s.vals.val.length ≤ st.core.vals.val.length + 1 := by
  obtain ⟨s, after, hs, hc, hp, hv, hl, hout⟩ := Simd.readFixed.complete
    {st.core with pos := next} (pops a) (output a) f.core.outer f.core.operands front
    f.core.vals f.core.base_eq hsize (by simpa only [Control.polymorphic, f.core.ctrls, List.getLast?_concat] using hr)
  refine ⟨s, by simp [metadataOperands, hd, hs], hp,
    ⟨f.core.output_of_same_ctrls hc hv (by simpa [Control.polymorphic] using hout),
      code.BodyState.blocks_eq_of_ctrls hc⟩, ?_⟩
  simp only [hv, f.core.vals, List.length_append]
  omega

/-- Lift a successful leaf reader through its accepting empty-visitor hook and
into the actual profile step, including its checked capacity guard. -/
theorem Frame.reader_step {st} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (opcode : U8) {A : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : Unit → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × Unit))
    (a : A) (s : code.OpIterState) (next : Usize) (out : List valtype)
    (hscalar : opcode.val ∉ controlOpcodes)
    (hdispatch : code.step_wasm2 code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st.core data env ctx opcode () =
      CoreVisitor.run read hook ())
    (hread : read = .ok (.Ok a, s)) (hhook : hook () s a = .ok (.Ok (), ()))
    (hpos : s.pos = next) (hout : f.Output out {st with core := s})
    (hlen : s.vals.val.length ≤ st.core.vals.val.length + 1)
    (hsize : st.core.vals.val.length < Usize.max) :
    ∃ final, step st data env profile ctx index opcode = .ok (.Ok (), final) ∧ final.core.pos = next ∧
      f.Output out final ∧ final.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  refine ⟨{st with core := s}, ?_, hpos, hout, hlen⟩
  rw [step.scalar_eq st data env profile ctx index opcode hscalar]
  have hn : alloc.vec.Vec.len st.core.vals ≠ core.num.Usize.MAX := by scalar_tac
  rw [if_neg hn, hdispatch]
  simp [CoreVisitor.run, hread, hhook, code.visit, core.result.Result.Insts.CoreOpsTry.branch]

theorem Frame.ref_null {st} {profile : ValidationProfile} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (rt : wasm_types.ElemType) (next : Usize) (front : List valtype)
    (hb : Wasm1.BytesAt data st.core.pos [ReferencesBinary.referenceByte rt] next)
    (hsize : st.core.vals.val.length < Usize.max)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands front) :
    ∃ s, step st data env profile ctx index 208#u8 = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ [valtype_reftype (Translate.referenceType rt)]) s ∧
      s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  obtain ⟨s, hs, hp, hout, hl⟩ := f.metadata_read (code.take_reference_type st.core data) rt next
    (fun _ => []) (fun rt => some (ModuleConstants.referenceValueType rt)) id front
    (code.take_reference_type.complete st.core data rt next hb) hsize (by simpa [Simd.inputTypes] using hr)
  rw [← code.read_ref_null.fixed] at hs
  exact f.reader_step data env ctx index 208#u8 _ _ rt s next _ (by decide)
    (code.step_wasm2.ref_null _ _ _ _ _ _) hs rfl hp
    (by cases rt <;> simpa [Simd.outputTypes, ModuleConstants.referenceValueType,
      Translate.referenceType, Translate.valueType, valtype_reftype] using hout) hl hsize

theorem Frame.table_get {st} {profile : ValidationProfile} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index idx : U32) (next : Usize) (front : List valtype)
    (hd : Leb128.Decoded data st.core.pos idx next) (hi : idx.val < env.table_types.val.length)
    (hsize : st.core.vals.val.length < Usize.max)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands
      (front ++ Simd.inputTypes ((fun _ => [.I32]) (idx, ModuleConstants.referenceValueType env.table_types.val[idx.val].elem)))) :
    ∃ s, step st data env profile ctx index 37#u8 = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ Simd.outputTypes ((fun a => some a.2) (idx, ModuleConstants.referenceValueType env.table_types.val[idx.val].elem))) s ∧
      s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  obtain ⟨s, hs, hp, hout, hl⟩ := f.metadata_read (code.take_table st.core data env)
    (idx, ModuleConstants.referenceValueType env.table_types.val[idx.val].elem) next
    (fun _ => [.I32]) (fun a => some a.2) Prod.fst front
    (code.take_table.complete st.core data env idx next hd hi) hsize hr
  rw [← code.read_table_get.fixed] at hs
  exact f.reader_step data env ctx index 37#u8 _ _ idx s next _ (by decide)
    (code.step_wasm2.table_get _ _ _ _ _ _) hs rfl hp hout hl hsize

theorem Frame.table_set {st} {profile : ValidationProfile} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index idx : U32) (next : Usize) (front : List valtype)
    (hd : Leb128.Decoded data st.core.pos idx next) (hi : idx.val < env.table_types.val.length)
    (hsize : st.core.vals.val.length < Usize.max)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands
      (front ++ Simd.inputTypes ((fun a => [a.2, .I32]) (idx, ModuleConstants.referenceValueType env.table_types.val[idx.val].elem)))) :
    ∃ s, step st data env profile ctx index 38#u8 = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ Simd.outputTypes ((fun _ => none) (idx, ModuleConstants.referenceValueType env.table_types.val[idx.val].elem))) s ∧
      s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  obtain ⟨s, hs, hp, hout, hl⟩ := f.metadata_read (code.take_table st.core data env)
    (idx, ModuleConstants.referenceValueType env.table_types.val[idx.val].elem) next
    (fun a => [a.2, .I32]) (fun _ => none) Prod.fst front
    (code.take_table.complete st.core data env idx next hd hi) hsize hr
  rw [← code.read_table_set.fixed] at hs
  exact f.reader_step data env ctx index 38#u8 _ _ idx s next _ (by decide)
    (code.step_wasm2.table_set _ _ _ _ _ _) hs rfl hp hout hl hsize

theorem Frame.table_grow {st} {profile : ValidationProfile} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index idx : U32) (middle : Usize) (hprefix : Leb128.Decoded data st.core.pos 15#u32 middle)
    (next : Usize) (front : List valtype)
    (hd : Leb128.Decoded data middle idx next) (hi : idx.val < env.table_types.val.length)
    (hsize : st.core.vals.val.length < Usize.max)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands
      (front ++ Simd.inputTypes ((fun a => [.I32, a.2]) (idx, ModuleConstants.referenceValueType env.table_types.val[idx.val].elem)))) :
    ∃ s, step st data env profile ctx index 252#u8 = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ Simd.outputTypes ((fun _ => some .I32) (idx, ModuleConstants.referenceValueType env.table_types.val[idx.val].elem))) s ∧
      s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  obtain ⟨s, hs, hp, hout, hl⟩ := f.metadata_read (code.take_table {st.core with pos := middle} data env)
    (idx, ModuleConstants.referenceValueType env.table_types.val[idx.val].elem) next
    (fun a => [.I32, a.2]) (fun _ => some .I32) Prod.fst front
    (code.take_table.complete {st.core with pos := middle} data env idx next hd hi) hsize hr
  rw [← code.read_table_grow.fixed] at hs
  exact f.reader_step data env ctx index 252#u8 _ _ idx s next _ (by decide)
    (by rw [code.step_wasm2.bulk _ _ _ _ _ 15#u32 middle _ hprefix (by decide), code.step_bulk.eq_runs]; rfl) hs rfl hp hout hl hsize

theorem Frame.table_size {st} {profile : ValidationProfile} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index idx : U32) (middle : Usize) (hprefix : Leb128.Decoded data st.core.pos 16#u32 middle)
    (next : Usize) (front : List valtype)
    (hd : Leb128.Decoded data middle idx next) (hi : idx.val < env.table_types.val.length)
    (hsize : st.core.vals.val.length < Usize.max)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands
      (front ++ Simd.inputTypes ((fun _ => []) (idx, ModuleConstants.referenceValueType env.table_types.val[idx.val].elem)))) :
    ∃ s, step st data env profile ctx index 252#u8 = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ Simd.outputTypes ((fun _ => some .I32) (idx, ModuleConstants.referenceValueType env.table_types.val[idx.val].elem))) s ∧
      s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  obtain ⟨s, hs, hp, hout, hl⟩ := f.metadata_read (code.take_table {st.core with pos := middle} data env)
    (idx, ModuleConstants.referenceValueType env.table_types.val[idx.val].elem) next
    (fun _ => []) (fun _ => some .I32) Prod.fst front
    (code.take_table.complete {st.core with pos := middle} data env idx next hd hi) hsize hr
  rw [← code.read_table_size.fixed] at hs
  exact f.reader_step data env ctx index 252#u8 _ _ idx s next _ (by decide)
    (by rw [code.step_wasm2.bulk _ _ _ _ _ 16#u32 middle _ hprefix (by decide), code.step_bulk.eq_runs]; rfl) hs rfl hp hout hl hsize

theorem Frame.table_fill {st} {profile : ValidationProfile} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index idx : U32) (middle : Usize) (hprefix : Leb128.Decoded data st.core.pos 17#u32 middle)
    (next : Usize) (front : List valtype)
    (hd : Leb128.Decoded data middle idx next) (hi : idx.val < env.table_types.val.length)
    (hsize : st.core.vals.val.length < Usize.max)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands
      (front ++ Simd.inputTypes ((fun a => [.I32, a.2, .I32]) (idx, ModuleConstants.referenceValueType env.table_types.val[idx.val].elem)))) :
    ∃ s, step st data env profile ctx index 252#u8 = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ Simd.outputTypes ((fun _ => none) (idx, ModuleConstants.referenceValueType env.table_types.val[idx.val].elem))) s ∧
      s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  obtain ⟨s, hs, hp, hout, hl⟩ := f.metadata_read (code.take_table {st.core with pos := middle} data env)
    (idx, ModuleConstants.referenceValueType env.table_types.val[idx.val].elem) next
    (fun a => [.I32, a.2, .I32]) (fun _ => none) Prod.fst front
    (code.take_table.complete {st.core with pos := middle} data env idx next hd hi) hsize hr
  rw [← code.read_table_fill.fixed] at hs
  exact f.reader_step data env ctx index 252#u8 _ _ idx s next _ (by decide)
    (by rw [code.step_wasm2.bulk _ _ _ _ _ 17#u32 middle _ hprefix (by decide), code.step_bulk.eq_runs]; rfl) hs rfl hp hout hl hsize

theorem Frame.typed_select {st} {profile : ValidationProfile} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (ty : wasm_types.ValueType) (count : List U8)
    (next : Usize) (front : List valtype)
    (he : Leb128.Encoding count 1) (hb : Wasm1.BytesAt data st.core.pos (count ++ [valueByte ty]) next)
    (hsize : st.core.vals.val.length < Usize.max)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands
      (front ++ [Translate.valueType ty, Translate.valueType ty, .I32])) :
    ∃ s, step st data env profile ctx index 28#u8 = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ [Translate.valueType ty]) s ∧
      s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  obtain ⟨middle, hcount, htag⟩ := hb.split
  have hread := hcount.take_index st.core 1#u32 he
  have htagread := code.take_value_type.complete {st.core with pos := middle} data ty next htag
  have hmeta : selectType st.core data = .ok (.Ok ty, {st.core with pos := next}) := by
    simp [selectType, hread, htagread]
  obtain ⟨s, hs, hp, hout, hl⟩ := f.metadata_read (selectType st.core data) ty next
    (fun ty => [.I32, ty, ty]) some id front hmeta hsize
    (by simpa [Simd.inputTypes, show Translate.valueType .I32 = valtype.I32 from rfl] using hr)
  rw [← code.read_typed_select.fixed] at hs
  exact f.reader_step data env ctx index 28#u8 _ _ ty s next _ (by decide)
    (code.step_wasm2.typed_select _ _ _ _ _ _) hs rfl hp (by simpa [Simd.outputTypes] using hout) hl hsize

/-- Completeness of ref.func requires the independent declaration premise in
addition to the ordinary generated function-index bound. -/
theorem Frame.ref_func {st} {profile : ValidationProfile} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index idx : U32) (next : Usize) (front : List valtype)
    (hd : Leb128.Decoded data st.core.pos idx next) (hi : idx.val < env.func_types.val.length)
    (hdecl : DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val))
      (.REF_FUNC (.mk_uN idx.val)))
    (hsize : st.core.vals.val.length < Usize.max)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands front) :
    ∃ s, step st data env profile ctx index 210#u8 = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ [.FUNCREF]) s ∧ s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  obtain ⟨bs, hbs, hbl, hbb, hbe⟩ := hd
  have hread := (Wasm1.BytesAt.mk hbs hbl hbb).take_index st.core idx hbe
  obtain ⟨i, himem, hie⟩ := List.mem_map.mp (DeclaredReferences.Instruction.ref_func_iff.mp hdecl)
  have heq : i = idx := UScalar.eq_of_val_eq (uN.mk_uN.inj hie)
  subst i
  obtain ⟨s, hs, hv, hc, hp⟩ := WP.spec_imp_exists
    (code.push_val.spec {st.core with pos := next} (.Val .FuncRef) hsize)
  have hrun : code.read_ref_func st.core data env = .ok (.Ok idx, s) := by
    simp [code.read_ref_func, hread, lift, Nat.not_le_of_gt hi, metadata.Env.declares_function.eq,
      himem, hs, core.result.Result.Insts.CoreOpsTry.branch]
  apply f.reader_step data env ctx index 210#u8 _ _ idx s next _ (by decide)
    (code.step_wasm2.ref_func _ _ _ _ _ _) hrun rfl hp ?_ ?_ hsize
  · refine ⟨f.core.output_of_same_ctrls hc (operands := f.core.operands ++ [.Val .FuncRef])
      (by simpa [f.core.vals, List.append_assoc] using hv) ?_, code.BodyState.blocks_eq_of_ctrls hc⟩
    simpa [f.core.poly_eq] using hr.snoc (.Val .FuncRef) .FUNCREF rfl
  · simp [hv]

theorem Frame.ref_is_null {st} {profile : ValidationProfile} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (rt : reftype) (next : Usize) (front : List valtype)
    (hb : Wasm1.BytesAt data st.core.pos [] next)
    (hsize : st.core.vals.val.length < Usize.max)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands
      (front ++ [valtype_reftype rt])) :
    ∃ s, step st data env profile ctx index 209#u8 = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ [.I32]) s ∧ s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  obtain ⟨t, popped, rest, hpop, hc, hp, hv, hl, ha, hout⟩ :=
    code.pop_stack_type.complete st.core f.core.outer f.core.operands front (valtype_reftype rt)
      f.core.vals f.core.base_eq (by simpa [f.core.poly_eq] using hr)
  have hcap : popped.vals.val.length < Usize.max := by
    simp only [hv, f.core.vals, List.length_append] at *
    omega
  obtain ⟨s, hs, hsv, hsc, hsp⟩ := WP.spec_imp_exists (code.push_val.spec popped (.Val .I32) hcap)
  have hrun : code.read_ref_is_null st.core = .ok (.Ok (), s) := by
    cases t with
    | Bot => simp [code.read_ref_is_null, hpop, hs, core.result.Result.Insts.CoreOpsTry.branch]
    | Val ty =>
      cases ty <;> cases rt <;> simp_all [Sequence.Accepts, Translate.valueType, valtype_reftype,
        code.read_ref_is_null, core.result.Result.Insts.CoreOpsTry.branch]
  apply f.reader_step data env ctx index 209#u8 _ _ () s next _ (by decide)
    (code.step_wasm2.ref_is_null _ _ _ _ _ _) hrun rfl (hsp.trans (hp.trans hb.empty.symm)) ?_ ?_ hsize
  · refine ⟨f.core.output_of_same_ctrls (hsc.trans hc) (operands := rest ++ [.Val .I32])
      (by simpa [hv, List.append_assoc] using hsv) ?_, code.BodyState.blocks_eq_of_ctrls (hsc.trans hc)⟩
    exact hout.snoc (.Val .I32) .I32 rfl
  · simp only [hsv, hv, f.core.vals, List.length_append, List.length_singleton]
    omega

end Itasca.Wasm2.Completeness
