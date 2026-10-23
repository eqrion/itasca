import Itasca.Wasm2.References.Operands
import Itasca.Wasm2.References.EnvMatches
import Itasca.Wasm2.Scalar.Step

/-!
# Preservation for reference and table instructions

`Pending.table_get`, `Pending.table_set`, `Pending.ref_null`, `Pending.ref_func`,
`Pending.typed_select`, `Pending.table_grow`, `Pending.table_size`, `Pending.table_fill`,
`Pending.data_drop`, `Pending.elem_drop` and `Pending.ref_is_null` show that the corresponding
extracted readers preserve the body invariant `Pending` (Wasm 2.0). `Pending.metadata_read` is the
shared argument for readers that decode metadata and then apply a fixed stack effect.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- A successful metadata decoder supplies byte provenance and a principal
effect; the shared fixed checker transports both through the typed zipper. -/
theorem Pending.metadata_read {data env profile locals index st} (p : Pending data env profile locals index st)
    {A B : Type}
    (decode : Result (core.result.Result A error.OpError × code.OpIterState))
    (pops : A → List types.ValueType) (output : A → Option types.ValueType)
    (metadata : A → B) (operation : A → instr)
    (hd : decode ⦃ r => r.2.vals = st.core.vals ∧ r.2.ctrls = st.core.ctrls ∧
      ∀ a, r.1 = .Ok a → At data p.start (.plain (operation a)) r.2.pos ⦄)
    (hw : ∀ a, wf_instr (operation a))
    (ht : ∀ a, (∃ s, decode = .ok (.Ok a, s)) → ∀ C,
      EnvTranslation.Matches env ⟨locals, p.ft.results⟩ C →
      Instr_ok C (operation a) (.mk_functype (.mk_list (Simd.inputTypes (pops a)))
        (.mk_list (Simd.outputTypes (output a)))))
    (hsize : st.core.vals.val.length < Usize.max) (hwasm2 : profile ≠ .Wasm1)
    (hdecl : ∀ a, DeclaredReferences.Instruction
      (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) (operation a) := by
        intro a
        simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) :
    metadataOperands decode pops output metadata ⦃ r =>
      (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, stack⟩ := id p.opened
  have hC := (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter
    (p.current.form.label p.current.ins p.current.outs)
  obtain ⟨⟨res, decoded⟩, hr, hvd, hcd, hed⟩ := WP.spec_imp_exists hd
  dsimp only at hvd hcd hed
  cases res with
  | Err e => simp [metadataOperands, hr]
  | Ok a =>
    have hbase : (Control.base decoded).val = outer.length := by
      simp [Control.base, hcd, ctrls, base]
    have hpoly : Control.polymorphic decoded = p.current.ctrl.polymorphic_base := by
      simp [Control.polymorphic, hcd, ctrls]
    obtain ⟨⟨res, out⟩, hrun, hc, hp, after, hva, hla, heffect⟩ := WP.spec_imp_exists
      (Simd.readFixed.segment decoded (pops a) (output a) outer p.current.vals
        (by simpa [hvd] using stack) hbase (by simpa [hvd] using hsize))
    dsimp only at hc hp hva hla heffect
    cases res with
    | Err e => simp [metadataOperands, hr, hrun]
    | Ok u =>
      cases u
      rw [WP.spec_equiv_exists]
      refine ⟨(.Ok (metadata a), out), by simp [metadataOperands, hr, hrun], fun _ => ?_⟩
      have htyped := (heffect rfl).wasm2_prefix _ hC.wf _ p.current.ops (operation a)
        (by simpa [hpoly, Frames.enter] using typed) (hw a) (ht a ⟨decoded, hr⟩ _ hC)
      apply p.append_result C outer spine header base {st with core := out} (operation a)
        p.current.ctrl.polymorphic_base after (hw a) (by simpa [hp] using hed a rfl)
        (by simpa [hpoly, Frames.enter] using htyped) ?_ ?_ hva (fun hp => absurd hp hwasm2)
        (hdecl a)
      · simpa [hc, hcd] using ctrls
      · simpa [code.BodyState.blocks_eq_of_ctrls (hc.trans hcd)] using blocks

theorem reference_value_translation (rt : types.ElemType) :
    Translate.valueType (ModuleConstants.referenceValueType rt) = valtype_reftype (Translate.referenceType rt) := by
  cases rt <;> rfl

theorem Pending.table_get {data env profile locals index st} (p : Pending data env profile locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 37#u8)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_table_get st.core data env ⦃ r => (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [code.read_table_get.fixed]
  apply p.metadata_read (hwasm2 := p.not_wasm1 hbyte (by decide))
    (code.take_table st.core data env) (fun _ => [.I32]) (fun a => some a.2) Prod.fst
    (fun a => .TABLE_GET (.mk_uN a.1.val)) ?_ ?_ ?_ hsize
  · apply WP.spec_mono (code.take_table.spec st.core data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    dsimp only at hv hc hd ⊢
    refine ⟨hv, hc, ?_⟩
    rintro ⟨idx, ty⟩ hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
    exact At.of_immediate p.inbounds hbyte p.pos (.reference (.tableGet idx hencoding))
      ⟨hbytes, hlen, hbound⟩
  · exact fun a => .instr_case_48 _ (EnvTranslation.index_wf a.1)
  · rintro ⟨idx, ty⟩ ⟨decoded, hrun⟩ C hC
    have hspec := code.take_table.spec st.core data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, hi, hty⟩ := hspec.2.2 idx ty rfl
    have htyped := hC.table_get idx env.table_types.val[idx.val] hi rfl
    simpa [Simd.inputTypes, Simd.outputTypes, hty, reference_value_translation, show Translate.valueType .I32 = valtype.I32 from rfl]
      using htyped

theorem Pending.table_set {data env profile locals index st} (p : Pending data env profile locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 38#u8)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_table_set st.core data env ⦃ r => (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [code.read_table_set.fixed]
  apply p.metadata_read (hwasm2 := p.not_wasm1 hbyte (by decide))
    (code.take_table st.core data env) (fun a => [a.2, .I32]) (fun _ => none) Prod.fst
    (fun a => .TABLE_SET (.mk_uN a.1.val)) ?_ ?_ ?_ hsize
  · apply WP.spec_mono (code.take_table.spec st.core data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    dsimp only at hv hc hd ⊢
    refine ⟨hv, hc, ?_⟩
    rintro ⟨idx, ty⟩ hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
    exact At.of_immediate p.inbounds hbyte p.pos (.reference (.tableSet idx hencoding))
      ⟨hbytes, hlen, hbound⟩
  · exact fun a => .instr_case_49 _ (EnvTranslation.index_wf a.1)
  · rintro ⟨idx, ty⟩ ⟨decoded, hrun⟩ C hC
    have hspec := code.take_table.spec st.core data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, hi, hty⟩ := hspec.2.2 idx ty rfl
    have htyped := hC.table_set idx env.table_types.val[idx.val] hi rfl
    simpa [Simd.inputTypes, Simd.outputTypes, hty, reference_value_translation, show Translate.valueType .I32 = valtype.I32 from rfl]
      using htyped

theorem Pending.ref_null {data env profile locals index st} (p : Pending data env profile locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 208#u8)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_ref_null st.core data ⦃ r => (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [code.read_ref_null.fixed]
  apply p.metadata_read (hwasm2 := p.not_wasm1 hbyte (by decide))
    (code.take_reference_type st.core data) (fun _ => [])
    (fun rt => some (ModuleConstants.referenceValueType rt)) id
    (fun rt => .REF_NULL (Translate.referenceType rt)) ?_ ?_ ?_ hsize
  · apply WP.spec_mono (code.take_reference_type.spec st.core data)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    exact ⟨hv, hc, fun rt hok => At.of_immediate p.inbounds hbyte p.pos
      (.reference (.refNull rt)) (hd rt hok)⟩
  · exact fun _ => .instr_case_40 _
  · intro rt _ C hC
    simpa [Simd.inputTypes, Simd.outputTypes, reference_value_translation] using
      Instr_ok.ref_null C (Translate.referenceType rt) hC.wf (.instr_case_40 _)

/-- The `ref.func` leaf uses the runtime declaration check independently of
its ordinary generated instruction typing. -/
theorem Pending.ref_func {data env profile locals index st} (p : Pending data env profile locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 210#u8)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_ref_func st.core data env ⦃ r =>
      ∀ idx, r.1 = .Ok idx → p.After {st with core := r.2} ∧
        DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val))
          (.REF_FUNC (.mk_uN idx.val)) ⦄ := by
  apply WP.spec_mono (code.read_ref_func.spec st.core data env hsize)
  rintro ⟨res, out⟩ ⟨hc, hout⟩ idx hok
  dsimp only at hc hout
  obtain ⟨hd, hi, hdecl, hv⟩ := hout idx hok
  refine ⟨?_, hdecl⟩
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, stack⟩ := id p.opened
  have hC := (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter
    (p.current.form.label p.current.ins p.current.outs)
  obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := hd
  apply p.append_result C outer spine header base {st with core := out}
    (.REF_FUNC (.mk_uN idx.val)) p.current.ctrl.polymorphic_base
    (p.current.vals ++ [.Val .FuncRef]) (.instr_case_41 _ (EnvTranslation.index_wf idx))
    (At.of_immediate p.inbounds hbyte p.pos (.reference (.refFunc idx hencoding))
      ⟨hbytes, hlen, hbound⟩) ?_ ?_ ?_ ?_ (fun hp => absurd hp (p.not_wasm1 hbyte (by decide)))
    hdecl
  · apply typed.append hC.wf _ (.instr_case_41 _ (EnvTranslation.index_wf idx))
    intro ts ht
    obtain ⟨front, hfront, rfl⟩ := (Sequence.realizes_append_concrete _ _ [.FuncRef] ts).mp ht
    exact ⟨front, hfront, by simpa [Frames.enter, Translate.valueType] using (Instrs_ok.frame _ _ front [] [.FUNCREF]
      (.instr _ _ [] [.FUNCREF] (hC.ref_func idx hi) hC.wf
        (.instr_case_41 _ (EnvTranslation.index_wf idx))) hC.wf
        (by simpa [Forall] using wf_instr.instr_case_41 _ (EnvTranslation.index_wf idx)))⟩
  · simpa [hc] using ctrls
  · simpa [code.BodyState.blocks_eq_of_ctrls hc] using blocks
  · simpa [stack, List.append_assoc] using hv

theorem Pending.typed_select {data env profile locals index st} (p : Pending data env profile locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 28#u8)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_typed_select st.core data ⦃ r => (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [code.read_typed_select.fixed]
  apply p.metadata_read (hwasm2 := p.not_wasm1 hbyte (by decide))
    (selectType st.core data) (fun ty => [.I32, ty, ty]) some id
    (fun ty => .SELECT (some [Translate.valueType ty])) ?_ ?_ ?_ hsize
  · apply WP.spec_mono (selectType.spec st.core data)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    refine ⟨hv, hc, ?_⟩
    intro ty hok
    obtain ⟨count, hb, he⟩ := hd ty hok
    exact At.of_immediate p.inbounds hbyte p.pos (.reference (.selectTyped ty he)) hb
  · exact fun _ => .instr_case_3 _
  · intro ty _ C hC
    simpa [Simd.inputTypes, Simd.outputTypes, show Translate.valueType .I32 = valtype.I32 from rfl] using
      Instr_ok.select_expl C (Translate.valueType ty) hC.wf (.instr_case_3 _)

theorem Pending.table_grow {data env profile locals index st} (p : Pending data env profile locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 15#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_table_grow {st.core with pos := next} data env ⦃ r =>
      (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [code.read_table_grow.fixed]
  apply p.metadata_read (hwasm2 := p.not_wasm1 hbyte (by decide))
    (code.take_table {st.core with pos := next} data env) (fun a => [.I32, a.2]) (fun _ => some .I32) Prod.fst
    (fun a => .TABLE_GROW (.mk_uN a.1.val)) ?_ ?_ ?_ hsize
  · apply WP.spec_mono (code.take_table.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    dsimp only at hv hc hd ⊢
    refine ⟨hv, hc, ?_⟩
    rintro ⟨idx, ty⟩ hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 15#u32 hpe (.tableGrow idx hencoding))
      ((Wasm1.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)
  · exact fun a => .instr_case_51 _ (EnvTranslation.index_wf a.1)
  · rintro ⟨idx, ty⟩ ⟨decoded, hrun⟩ C hC
    have hspec := code.take_table.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, hi, hty⟩ := hspec.2.2 idx ty rfl
    have htyped := hC.table_grow idx env.table_types.val[idx.val] hi rfl
    simpa [Simd.inputTypes, Simd.outputTypes, hty, reference_value_translation,
      show Translate.valueType .I32 = valtype.I32 from rfl] using htyped

theorem Pending.table_size {data env profile locals index st} (p : Pending data env profile locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 16#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_table_size {st.core with pos := next} data env ⦃ r =>
      (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [code.read_table_size.fixed]
  apply p.metadata_read (hwasm2 := p.not_wasm1 hbyte (by decide))
    (code.take_table {st.core with pos := next} data env) (fun _ => []) (fun _ => some .I32) Prod.fst
    (fun a => .TABLE_SIZE (.mk_uN a.1.val)) ?_ ?_ ?_ hsize
  · apply WP.spec_mono (code.take_table.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    dsimp only at hv hc hd ⊢
    refine ⟨hv, hc, ?_⟩
    rintro ⟨idx, ty⟩ hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 16#u32 hpe (.tableSize idx hencoding))
      ((Wasm1.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)
  · exact fun a => .instr_case_50 _ (EnvTranslation.index_wf a.1)
  · rintro ⟨idx, ty⟩ ⟨decoded, hrun⟩ C hC
    have hspec := code.take_table.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, hi, hty⟩ := hspec.2.2 idx ty rfl
    have htyped := hC.table_size idx env.table_types.val[idx.val] hi rfl
    simpa [Simd.inputTypes, Simd.outputTypes, hty, reference_value_translation,
      show Translate.valueType .I32 = valtype.I32 from rfl] using htyped

theorem Pending.table_fill {data env profile locals index st} (p : Pending data env profile locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 17#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_table_fill {st.core with pos := next} data env ⦃ r =>
      (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [code.read_table_fill.fixed]
  apply p.metadata_read (hwasm2 := p.not_wasm1 hbyte (by decide))
    (code.take_table {st.core with pos := next} data env) (fun a => [.I32, a.2, .I32]) (fun _ => none) Prod.fst
    (fun a => .TABLE_FILL (.mk_uN a.1.val)) ?_ ?_ ?_ hsize
  · apply WP.spec_mono (code.take_table.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    dsimp only at hv hc hd ⊢
    refine ⟨hv, hc, ?_⟩
    rintro ⟨idx, ty⟩ hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 17#u32 hpe (.tableFill idx hencoding))
      ((Wasm1.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)
  · exact fun a => .instr_case_52 _ (EnvTranslation.index_wf a.1)
  · rintro ⟨idx, ty⟩ ⟨decoded, hrun⟩ C hC
    have hspec := code.take_table.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, hi, hty⟩ := hspec.2.2 idx ty rfl
    have htyped := hC.table_fill idx env.table_types.val[idx.val] hi rfl
    simpa [Simd.inputTypes, Simd.outputTypes, hty, reference_value_translation,
      show Translate.valueType .I32 = valtype.I32 from rfl] using htyped

theorem Pending.data_drop {data env profile locals index st} (p : Pending data env profile locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 9#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.take_data_index {st.core with pos := next} data env ⦃ r =>
      (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [← metadataOperands.empty (code.take_data_index {st.core with pos := next} data env)]
  apply p.metadata_read (hwasm2 := p.not_wasm1 hbyte (by decide))
    _ (fun _ => []) (fun _ => none) id
    (fun idx => .DATA_DROP (.mk_uN idx.val)) ?_ ?_ ?_ hsize
  · apply WP.spec_mono (code.take_data_index.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    refine ⟨hv, hc, ?_⟩
    intro idx hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx hok).1
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 9#u32 hpe (.dataDrop idx hencoding))
      ((Wasm1.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)
  · exact fun a => .instr_case_67 _ (EnvTranslation.index_wf a)
  · rintro idx ⟨decoded, hrun⟩ C hC
    have hspec := code.take_data_index.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, count, hc, hi⟩ := hspec.2.2 idx rfl
    exact hC.data_drop idx count hc hi

theorem Pending.elem_drop {data env profile locals index st} (p : Pending data env profile locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 13#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.take_element {st.core with pos := next} data env ⦃ r =>
      (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [← metadataOperands.empty (code.take_element {st.core with pos := next} data env)]
  apply p.metadata_read (hwasm2 := p.not_wasm1 hbyte (by decide))
    _ (fun _ => []) (fun _ => none) id
    (fun a => .ELEM_DROP (.mk_uN a.1.val)) ?_ ?_ ?_ hsize
  · apply WP.spec_mono (code.take_element.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    refine ⟨hv, hc, ?_⟩
    rintro ⟨idx, ty⟩ hok
    obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 13#u32 hpe (.elemDrop idx hencoding))
      ((Wasm1.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)
  · exact fun a => .instr_case_55 _ (EnvTranslation.index_wf a.1)
  · rintro ⟨idx, ty⟩ ⟨decoded, hrun⟩ C hC
    have hspec := code.take_element.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, hi, hty⟩ := hspec.2.2 idx ty rfl
    exact hC.elem_drop idx env.elements.val[idx.val] hi rfl

theorem Pending.ref_is_null {data env profile locals index st} (p : Pending data env profile locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 209#u8)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_ref_is_null st.core ⦃ r => (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, stack⟩ := id p.opened
  have hC := (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter
    (p.current.form.label p.current.ins p.current.outs)
  have hbase : (Control.base st.core).val = outer.length := by simp [Control.base, ctrls, base]
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  apply WP.spec_mono (code.read_ref_is_null.segment st.core outer p.current.vals stack hbase hsize)
  rintro ⟨res, out⟩ ⟨hc, hp, after, hv, heffect⟩ ⟨u, hok⟩
  dsimp only at hc hp hv heffect
  cases u
  obtain ⟨rt, he⟩ := heffect hok
  have htyped := he.wasm2_prefix _ hC.wf _ p.current.ops .REF_IS_NULL
    (by simpa [hpoly, Frames.enter] using typed) .instr_case_42
    (by simpa [Simd.inputTypes, Simd.outputTypes, reference_value_translation,
      show Translate.valueType .I32 = valtype.I32 from rfl] using
      Instr_ok.ref_is_null _ (Translate.referenceType rt) hC.wf .instr_case_42)
  apply p.append_result C outer spine header base {st with core := out} .REF_IS_NULL
    p.current.ctrl.polymorphic_base after .instr_case_42 ?_
    (by simpa [hpoly, Frames.enter] using htyped) ?_ ?_ hv
    (fun hp => absurd hp (p.not_wasm1 hbyte (by decide)))
  · apply At.of_immediate p.inbounds hbyte p.pos (.reference .refIsNull)
    exact ⟨by simp [hp], by simp [hp], by have := p.pos; have := p.inbounds; simp only [hp]; omega⟩
  · simpa [hc] using ctrls
  · simpa [code.BodyState.blocks_eq_of_ctrls hc] using blocks

end Itasca.Wasm2
