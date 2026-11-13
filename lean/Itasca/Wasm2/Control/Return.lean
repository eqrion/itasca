import Itasca.Wasm2.Control.FuncType
import Itasca.Wasm2.TableAdapters
import Itasca.Wasm2.EmptyVisitorLoop
import Itasca.Handler.Select
import Itasca.Handler.RawControl
import Itasca.Binary.Wasm1.DeclaredReferences
import Itasca.Wasm2.Scalar.ReaderPost
import Itasca.Wasm2.Control.BranchComplete
import Itasca.Wasm2.LoopDispatch

/-!
Sections, each formerly its own module: Call, BranchStep, Return.
-/

/-! ## Call -/

section

/-!
# Calls

Soundness and completeness of the extracted `code.call` for `call` and `call_indirect`.
`code.call.direct_prefix` and `code.call.indirect_prefix` extend a `TypedPrefix` across an accepted
call, and `code.call.direct_complete` and `code.call.indirect_complete` accept independently
encoded indices with compatible operands. Both are stated against the generated Wasm 2.0 rules.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- Direct-call acceptance consumes every parameter and supplies every result,
with the function index certified by the independent LEB grammar. -/
theorem code.call.direct_prefix (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.core.vals.val = outer ++ segment)
    (hbase : (Control.base st.core).val = outer.length)
    (C : context) (hC : EnvTranslation.Matches env ctx C) (inputs : List valtype) (ops : List instr)
    (htyped : Wasm2.TypedPrefix C inputs ops (Control.polymorphic st.core) segment) :
    code.call st data env false ⦃ r => r.1 = .Ok () →
      ∃ idx, Leb128.Decoded data st.core.pos idx r.2.core.pos ∧
      r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧
      ∃ rest, r.2.core.vals.val = outer ++ rest ∧
        Wasm2.TypedPrefix C inputs (ops ++ [.CALL (.mk_uN idx.val)])
          (Control.polymorphic st.core) rest ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  cases r with
  | Err e => simp [code.call.eq_core, Wasm2.callCore, hr]
  | Ok pair =>
    obtain ⟨idx, next⟩ := pair
    by_cases hi : idx.val < env.func_types.val.length
    · have hix : (UScalar.cast .Usize idx).val < env.func_types.val.length := by simpa using hi
      obtain ⟨ft, hft, heq⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec env.func_types (UScalar.cast .Usize idx) hix)
      have htype : env.func_types.val[idx.val] = ft := by simpa using heq.symm
      have hsmall := Nat.not_le_of_gt hi
      obtain ⟨⟨res, s⟩, hs, hout⟩ := WP.spec_imp_exists
        (code.apply_func_type.realizes { st.core with pos := next } ft outer segment hvals hbase)
      cases res with
      | Err e => simp [code.call.eq_core, Wasm2.callCore, hr, lift, hsmall, hft, hs]
      | Ok u =>
        obtain ⟨hc, hp, _, _, rest, hv, _, ht⟩ := hout rfl
        dsimp only at hc hp hv ht
        have ht' : ∀ ts, Sequence.Realizes (Control.polymorphic st.core) rest ts →
            Sequence.Realizes (Control.polymorphic st.core) segment
              (ts ++ ft.params.val.map Translate.valueType) := ht
        have htyping := (Wasm2.ResumePrefix.after_pop htyped ht').finish hC.wf
          (.CALL (.mk_uN idx.val)) ft.results.val (.instr_case_10 _ (EnvTranslation.index_wf idx))
          (hC.call idx ft hi htype)
        rw [WP.spec_equiv_exists]
        refine ⟨(.Ok (), ⟨s⟩), ?_, fun _ => ?_⟩
        · simp [code.call.eq_core, Wasm2.callCore, hr, lift, hsmall, hft, hs]
        · exact ⟨idx, by simpa [hp, Leb128.Post] using hd, hc, code.BodyState.blocks_eq_of_ctrls hc, _, hv, htyping⟩
    · have hlarge := Nat.le_of_not_gt hi
      simp [code.call.eq_core, Wasm2.callCore, hr, lift, hlarge]

/-- Direct calls accept independently encoded, in-range function indices and
compatible operands within the explicit signature and operand capacity limits. -/
theorem code.call.direct_complete (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (idx : U32) (next : Usize) (ft : wasm_types.FuncType)
    (hd : Leb128.Decoded data st.core.pos idx next)
    (hi : idx.val < env.func_types.val.length) (ht : env.func_types.val[idx.val] = ft)
    (hp : ft.params.val.length ≤ 1000) (hr : ft.results.val.length ≤ 1000)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.core.vals.val = outer ++ segment) (hb : (Control.base st.core).val = outer.length)
    (hcap : st.core.vals.val.length + ft.results.val.length ≤ Usize.max)
    (hreal : Sequence.Realizes (Control.polymorphic st.core) segment
      (before ++ ft.params.val.map Translate.valueType)) :
    code.call st data env false ⦃ r => r.1 = .Ok () ∧
      r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧ r.2.core.pos = next ∧
      ∃ rest, r.2.core.vals.val = outer ++ rest ∧
        rest.length ≤ segment.length + ft.results.val.length ∧
        Sequence.Realizes (Control.polymorphic st.core) rest
          (before ++ ft.results.val.map Translate.valueType) ⦄ := by
  have hread := reader.read_u32_leb.complete data st.core.pos idx next hd
  have hix : (UScalar.cast .Usize idx).val < env.func_types.val.length := by simpa using hi
  obtain ⟨ft', hft, heq⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec env.func_types (UScalar.cast .Usize idx) hix)
  have he : ft' = ft := by simpa [ht] using heq
  subst ft'
  obtain ⟨⟨_, s⟩, hs, rfl, hc, hpos, rest, hvs, hlen, hreal'⟩ := WP.spec_imp_exists
    (code.apply_func_type.complete { st.core with pos := next } ft outer segment before
      hp hr hv hb hcap hreal)
  have hsmall := Nat.not_le_of_gt hi
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok (), ⟨s⟩), ?_, rfl, hc, code.BodyState.blocks_eq_of_ctrls hc, hpos, rest, hvs, hlen, hreal'⟩
  simp [code.call.eq_core, Wasm2.callCore, hread, lift, hsmall, hft, ht, hs]

/-- Indirect calls decode both indices and require a function-reference table.
The selector is consumed before function arguments. -/
theorem code.call.indirect_prefix (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.core.vals.val = outer ++ segment)
    (hbase : (Control.base st.core).val = outer.length)
    (C : context) (hC : EnvTranslation.Matches env ctx C) (inputs : List valtype) (ops : List instr)
    (htyped : Wasm2.TypedPrefix C inputs ops (Control.polymorphic st.core) segment) :
    code.call st data env true ⦃ r => r.1 = .Ok () →
      ∃ idx table middle, Leb128.Decoded data st.core.pos idx middle ∧
      Leb128.Decoded data middle table r.2.core.pos ∧
      r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧
      ∃ rest, r.2.core.vals.val = outer ++ rest ∧
        Wasm2.TypedPrefix C inputs (ops ++ [.CALL_INDIRECT (.mk_uN table.val) (.mk_uN idx.val)])
          (Control.polymorphic st.core) rest ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  cases r with
  | Err e => simp [code.call, code.call_indirect_info, code.take_index, hr,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨idx, middle⟩ := pair
    obtain ⟨rtable, hreadtable, hdtable⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data middle)
    cases rtable with
    | Err e => simp [code.call, code.call_indirect_info, code.take_index, hr, hreadtable,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨table, next⟩ := pair
      by_cases htable : table.val < env.table_types.val.length
      · have htix : (UScalar.cast .Usize table).val < env.table_types.val.length := by simpa using htable
        obtain ⟨tt, hget, hgeteq⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.index_usize_spec env.table_types (UScalar.cast .Usize table) htix)
        have htt : env.table_types.val[table.val] = tt := by simpa using hgeteq.symm
        have htablesmall := Nat.not_le_of_gt htable
        cases helem : tt.elem with
        | ExternRef =>
          simp [code.call, code.call_indirect_info, code.take_index, hr, hreadtable, lift,
            htablesmall, hget, helem, wasm_types.ElemType.value_type,
            core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
            wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq,
            core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | FuncRef =>
          have hfun : env.table_types.val[table.val].elem = .FuncRef := by rw [htt]; exact helem
          by_cases hi : idx.val < env.types.val.length
          · have hix : (UScalar.cast .Usize idx).val < env.types.val.length := by simpa using hi
            obtain ⟨ft, hft, heq⟩ := WP.spec_imp_exists
              (alloc.vec.Vec.index_usize_spec env.types (UScalar.cast .Usize idx) hix)
            have htype : env.types.val[idx.val] = ft := by simpa using heq.symm
            have hsmall := Nat.not_le_of_gt hi
            obtain ⟨⟨rc, sc⟩, hcond, hcc, hpc, condrest, hvc, _, htc⟩ := WP.spec_imp_exists
              (code.pop_with_type.realizes { st.core with pos := next } outer segment .I32 hvals hbase)
            dsimp only at hcc hpc hvc htc
            cases rc with
            | Err e =>
              simp [code.call, code.call_indirect_info, code.take_index, hr, hreadtable, lift,
                htablesmall, hget, helem, wasm_types.ElemType.value_type,
                core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hsmall, hcond,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok popped =>
              obtain ⟨⟨res, s⟩, hs, hout⟩ := WP.spec_imp_exists
                (code.apply_func_type.realizes sc ft outer condrest hvc
                  (by simpa [Control.base, hcc] using hbase))
              cases res with
              | Err e =>
                simp [code.call, code.call_indirect_info, code.take_index, hr, hreadtable, lift,
                  htablesmall, hget, helem, wasm_types.ElemType.value_type,
                  core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                  wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hsmall, hcond, hft, hs,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              | Ok u =>
                obtain ⟨hc, hp, _, _, rest, hv, _, ht⟩ := hout rfl
                dsimp only at hc hp hv ht
                have htransfer : ∀ ts, Sequence.Realizes (Control.polymorphic st.core) rest ts →
                    Sequence.Realizes (Control.polymorphic st.core) segment
                      (ts ++ (ft.params.val.map Translate.valueType ++ [.I32])) := by
                  intro ts hts
                  have hparam := ht ts (by simpa [Control.polymorphic, hcc] using hts)
                  have hargs := htc.2 _ (by simpa [Control.polymorphic, hcc] using hparam)
                  simpa [Translate.valueType, List.append_assoc, Control.polymorphic] using hargs
                have htyping := (Wasm2.ResumePrefix.after_pop htyped htransfer).finish hC.wf
                  (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN idx.val)) ft.results.val
                  (.instr_case_11 _ _ (EnvTranslation.index_wf table) (EnvTranslation.index_wf idx))
                  (hC.call_indirect idx table ft hi htype htable hfun)
                rw [WP.spec_equiv_exists]
                refine ⟨(.Ok (), ⟨s⟩), ?_, fun _ => ?_⟩
                · simp [code.call, code.call_indirect_info, code.take_index, hr, hreadtable, lift,
                    htablesmall, hget, helem, wasm_types.ElemType.value_type,
                    core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                    wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hsmall, hcond, hft, hs,
                    core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                · exact ⟨idx, table, middle, hd, by simpa [Leb128.Post, hp, hpc] using hdtable,
                    hc.trans hcc, code.BodyState.blocks_eq_of_ctrls (hc.trans hcc), _, hv, htyping⟩
          · have hlarge := Nat.le_of_not_gt hi
            simp [code.call, code.call_indirect_info, code.take_index, hr, hreadtable, lift,
              htablesmall, hget, helem, wasm_types.ElemType.value_type,
              core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
              wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hlarge,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · have hlarge := Nat.le_of_not_gt htable
        simp [code.call, code.call_indirect_info, code.take_index, hr, hreadtable, lift,
          hlarge, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Independently encoded indices and compatible operands force acceptance. -/
theorem code.call.indirect_complete (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (idx table : U32) (middle next : Usize)
    (ft : wasm_types.FuncType) (hd : Leb128.Decoded data st.core.pos idx middle)
    (hdtable : Leb128.Decoded data middle table next)
    (htable : table.val < env.table_types.val.length)
    (hfun : env.table_types.val[table.val].elem = .FuncRef)
    (hi : idx.val < env.types.val.length) (ht : env.types.val[idx.val] = ft)
    (hp : ft.params.val.length ≤ 1000) (hr : ft.results.val.length ≤ 1000)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.core.vals.val = outer ++ segment) (hb : (Control.base st.core).val = outer.length)
    (hcap : st.core.vals.val.length + ft.results.val.length ≤ Usize.max)
    (hreal : Sequence.Realizes (Control.polymorphic st.core) segment
      (before ++ (ft.params.val.map Translate.valueType ++ [.I32]))) :
    code.call st data env true ⦃ r => r.1 = .Ok () ∧
      r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧ r.2.core.pos = next ∧
      ∃ rest, r.2.core.vals.val = outer ++ rest ∧
        rest.length ≤ segment.length + ft.results.val.length ∧
        Sequence.Realizes (Control.polymorphic st.core) rest
          (before ++ ft.results.val.map Translate.valueType) ⦄ := by
  have hread := reader.read_u32_leb.complete data st.core.pos idx middle hd
  have hreadtable := reader.read_u32_leb.complete data middle table next hdtable
  have htix : (UScalar.cast .Usize table).val < env.table_types.val.length := by simpa using htable
  obtain ⟨tt, hget, hgeteq⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec env.table_types (UScalar.cast .Usize table) htix)
  have helem : tt.elem = .FuncRef := by simpa [hgeteq] using hfun
  have htablesmall := Nat.not_le_of_gt htable
  have hix : (UScalar.cast .Usize idx).val < env.types.val.length := by simpa using hi
  obtain ⟨ft', hft, heq⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec env.types (UScalar.cast .Usize idx) hix)
  have he : ft' = ft := by simpa [ht] using heq
  subst ft'
  obtain ⟨_, sc, condrest, hcond, hcc, hpc, hvc, hlc, _, htc⟩ :=
    code.pop_with_type.complete { st.core with pos := next } outer segment
      (before ++ ft.params.val.map Translate.valueType) .I32 hv hb
      (by simpa [Translate.valueType, List.append_assoc, Control.polymorphic] using hreal)
  have hcap' : sc.vals.val.length + ft.results.val.length ≤ Usize.max := by
    simp only [hvc, hv, List.length_append] at *
    omega
  obtain ⟨⟨_, s⟩, hs, rfl, hc, hpos, rest, hvs, hlen, hreal'⟩ := WP.spec_imp_exists
    (code.apply_func_type.complete sc ft outer condrest before hp hr hvc
      (by simpa [Control.base, hcc] using hb) hcap'
      (by simpa [Control.polymorphic, hcc] using htc))
  have hsmall := Nat.not_le_of_gt hi
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok (), ⟨s⟩), ?_, rfl, hc.trans hcc, code.BodyState.blocks_eq_of_ctrls (hc.trans hcc), hpos.trans hpc,
    rest, hvs, by omega, ?_⟩
  · simp [code.call, code.call_indirect_info, code.take_index, hread, hreadtable, lift,
      htablesmall, hget, helem, wasm_types.ElemType.value_type,
      core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hsmall, hcond, hft, ht, hs,
      core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simpa [Control.polymorphic, hcc] using hreal'

end Itasca

end

/-! ## BranchStep -/

section

/-!
# Branch, `br_table` and call steps

`Pending` preservation for the opcodes `call` (`0x10`), `call_indirect` (`0x11`), `br` (`0x0c`),
`br_if` (`0x0d`) and `br_table` (`0x0e`). Each of `Pending.call`, `Pending.call_indirect`,
`Pending.branch`, `Pending.branch_if` and `Pending.branch_table` combines the handler's prefix
theorem with `Pending.append_result`. `Frames.Open.branchLabels` supplies the label agreement they
all need.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- In a zipper whose root has no labels, the runtime labels agree with the context's. -/
theorem Frames.Open.branchLabels {env root st parents current}
    (h : Frames.Open env root st parents current) (hroot : root.LABELS = [])
    (C : context) (outer : List code.StackType)
    (spine : Frames.Spine env root parents C outer current.form current.ins) :
    BranchLabels env st (Frames.enter C current.form current.ins current.outs) := by
  intro depth view hl
  have hd : depth.val < st.blocks.val.length := by
    by_contra hn
    simp_all [labelAt]
  have he := Frames.Open.labels h depth.val
  obtain ⟨C', outer', spine', header, base, typed, ctrls, blocks, vals⟩ := h
  have hd' : depth.val < (Frames.labels (parents ++ [current])).length := by
    simpa [Frames.labels, blocks] using hd
  rw [hl] at he
  cases hr : resolve env view with
  | none => simp [hr, List.getElem?_eq_getElem hd'] at he
  | some ts =>
    refine ⟨ts, rfl, ?_⟩
    have hcontext : (Frames.enter C current.form current.ins current.outs).LABELS =
        Frames.labels (parents ++ [current]) := by
      simp [Frames.enter, Control.labelContext_labels, spine.labels, hroot, Frames.labels]
    simpa [hr, hcontext] using he.symm

/-- The direct `call` opcode (`0x10`) preserves `Pending` on success. -/
theorem Pending.call_reader {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x10#u8) :
    code.call st data env false ⦃ r => r.1 = .Ok () → ∃ idx values, Leb128.Decoded data st.core.pos idx r.2.core.pos ∧
      ReaderPost p r.2.core (.CALL (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC := (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter
    (p.current.form.label p.current.ins p.current.outs)
  apply WP.spec_mono (code.call.direct_prefix st data env ⟨locals, p.ft.results⟩ outer
    p.current.vals vals (by simp [Control.base, ctrls, base]) _ hC _ p.current.ops
    (by simpa [hpoly, Frames.enter] using typed))
  intro r hr hok
  obtain ⟨idx, hd, hc, hb, rest, hv, ht⟩ := hr hok
  have encoded : Wasm1.At data p.start (.plain (.CALL (.mk_uN idx.val))) r.2.core.pos :=
    .of_u32 idx p.inbounds hbyte p.pos (fun _ => .call idx) hd
  refine ⟨idx, rest, hd, ?_⟩
  apply p.append_reader_context C outer spine header base r.2.core (.CALL (.mk_uN idx.val))
    p.current.ctrl.polymorphic_base rest (.instr_case_10 _ (EnvTranslation.index_wf idx))
    (.plain encoded) (by simpa [hpoly, Frames.enter] using ht) _ (by simpa [hb] using blocks) hv
    (encoded.declared _)
  simpa [hc] using ctrls
/-- Forward preservation projects the shared exact reader certificate. -/
theorem Pending.call {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x10#u8) :
    code.call st data env false ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  apply WP.spec_mono (p.call_reader hbyte)
  intro r effect accepted
  rcases effect accepted with ⟨_, _, _, post⟩
  exact post.after

/-- The `call_indirect` opcode (`0x11`) preserves `Pending` on success. -/
theorem Pending.call_indirect_reader {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x11#u8) :
    code.call st data env true ⦃ r => r.1 = .Ok () → ∃ idx table middle values, Leb128.Decoded data st.core.pos idx middle ∧
      Leb128.Decoded data middle table r.2.core.pos ∧
      ReaderPost p r.2.core (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC := (spine.matches (EnvTranslation.Matches.root env ⟨locals, p.ft.results⟩)).enter
    (p.current.form.label p.current.ins p.current.outs)
  apply WP.spec_mono (code.call.indirect_prefix st data env ⟨locals, p.ft.results⟩ outer
    p.current.vals vals (by simp [Control.base, ctrls, base]) _ hC _ p.current.ops
    (by simpa [hpoly, Frames.enter] using typed))
  intro r hr hok
  obtain ⟨idx, table, middle, hd, hdtable, hc, hb, rest, hv, ht⟩ := hr hok
  obtain ⟨typeBytes, hts, htl, htb, hte⟩ := hd
  obtain ⟨tableBytes, hss, hsl, hsb, hse⟩ := hdtable
  have hbytes := (Wasm1.BytesAt.mk hts htl htb).append (Wasm1.BytesAt.mk hss hsl hsb)
  refine ⟨idx, table, middle, rest, ?_, ?_, ?_⟩
  · exact ⟨typeBytes, hts, htl, htb, hte⟩
  · exact ⟨tableBytes, hss, hsl, hsb, hse⟩
  · apply p.append_reader_context C outer spine header base r.2.core (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN idx.val))
      p.current.ctrl.polymorphic_base rest
      (.instr_case_11 _ _ (EnvTranslation.index_wf table) (EnvTranslation.index_wf idx))
      (.of_immediate p.inbounds hbyte p.pos (.reference (.callIndirect idx table hte hse)) hbytes)
      (by simpa [hpoly, Frames.enter] using ht) _ (by simpa [hb] using blocks) hv
      (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices])
    simpa [hc] using ctrls
/-- Forward preservation projects the shared exact reader certificate. -/
theorem Pending.call_indirect {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x11#u8) :
    code.call st data env true ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  apply WP.spec_mono (p.call_indirect_reader hbyte)
  intro r effect accepted
  rcases effect accepted with ⟨_, _, _, _, _, _, post⟩
  exact post.after

/-- The `br` opcode (`0x0c`) preserves `Pending` on success. -/
theorem Pending.branch_reader {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x0C#u8) :
    code.branch st data env false ⦃ r => r.1 = .Ok () → ∃ depth, Leb128.Decoded data st.core.pos depth r.2.core.pos ∧
      ReaderPost p r.2.core (.BR (.mk_uN depth.val)) true [] ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hC := Frames.enter_wf C (spine.context_wf (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have hl := p.opened.branchLabels rfl C outer spine
  apply WP.spec_mono (code.branch.prefix st data env (p.parents.map Frames.Saved.ctrl)
    p.current.ctrl outer p.current.vals ctrls vals base p.opened.shape.aligned
    _ hC _ p.current.ops typed hl)
  intro r hr hok
  obtain ⟨depth, hd, hv, hb, hc, ht⟩ := hr hok
  have encoded : Wasm1.At data p.start (.plain (.BR (.mk_uN depth.val))) r.2.core.pos :=
    .of_u32 depth p.inbounds hbyte p.pos (fun _ => .br depth) hd
  refine ⟨depth, hd, ?_⟩
  exact p.append_reader_context C outer spine header base r.2.core (.BR (.mk_uN depth.val)) true []
    (.instr_case_7 _ (Spec.label_wf depth)) (.plain encoded) ht hc
    (by simpa [hb] using blocks) (by simpa using hv) (encoded.declared _)
/-- Forward preservation projects the shared exact reader certificate. -/
theorem Pending.branch {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x0C#u8) :
    code.branch st data env false ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  apply WP.spec_mono (p.branch_reader hbyte)
  intro r effect accepted
  rcases effect accepted with ⟨_, _, post⟩
  exact post.after

/-- The `br_if` opcode (`0x0d`) preserves `Pending` on success. -/
theorem Pending.branch_if_reader {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x0D#u8) :
    code.branch st data env true ⦃ r => r.1 = .Ok () → ∃ depth values, Leb128.Decoded data st.core.pos depth r.2.core.pos ∧
      ReaderPost p r.2.core (.BR_IF (.mk_uN depth.val)) p.current.ctrl.polymorphic_base values ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hC := Frames.enter_wf C (spine.context_wf (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have hl := p.opened.branchLabels rfl C outer spine
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  apply WP.spec_mono (code.branch.conditional_prefix st data env outer p.current.vals vals
    (by simp [Control.base, ctrls, base]) p.opened.shape.core p.opened.shape.aligned
    _ hC _ p.current.ops (by simpa [hpoly, Frames.enter] using typed) hl)
  intro r hr hok
  obtain ⟨depth, hd, hc, hb, rest, hv, ht⟩ := hr hok
  have encoded : Wasm1.At data p.start (.plain (.BR_IF (.mk_uN depth.val))) r.2.core.pos :=
    .of_u32 depth p.inbounds hbyte p.pos (fun _ => .brIf depth) hd
  refine ⟨depth, rest, hd, ?_⟩
  apply p.append_reader_context C outer spine header base r.2.core (.BR_IF (.mk_uN depth.val))
    p.current.ctrl.polymorphic_base rest (.instr_case_8 _ (Spec.label_wf depth))
    (.plain encoded) (by simpa [hpoly, Frames.enter] using ht) _ (by simpa [hb] using blocks) hv
    (encoded.declared _)
  simpa [hc] using ctrls
/-- Forward preservation projects the shared exact reader certificate. -/
theorem Pending.branch_if {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x0D#u8) :
    code.branch st data env true ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  apply WP.spec_mono (p.branch_if_reader hbyte)
  intro r effect accepted
  rcases effect accepted with ⟨_, _, _, post⟩
  exact post.after

end Itasca.Wasm2

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- The `br_table` opcode (`0x0e`) preserves `Pending` on success. -/
theorem Pending.branch_table_reader {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x0E#u8) :
    code.branch_table st data env ⦃ r => r.1 = .Ok () → ∃ depths fallback, BrTable.Decoded data st.core.pos depths fallback r.2.core.pos ∧
      ReaderPost p r.2.core (BrTable.instruction depths fallback) true [] ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hC := Frames.enter_wf C (spine.context_wf (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have hl := p.opened.branchLabels rfl C outer spine
  apply WP.spec_mono (code.branch_table.prefix st data env (p.parents.map Frames.Saved.ctrl)
    p.current.ctrl outer p.current.vals ctrls vals base p.opened.shape.core
    _ hC _ p.current.ops typed hl)
  intro r hr hok
  obtain ⟨depths, default, hd, hv, hb, hc, ht⟩ := hr hok
  have encoded : Wasm1.At data p.start (.plain (BrTable.instruction depths default)) r.2.core.pos :=
    .of_table_decoded depths default p.inbounds hbyte p.pos hd
  refine ⟨depths, default, hd, ?_⟩
  exact p.append_reader_context C outer spine header base r.2.core (BrTable.instruction depths default) true []
    (BrTable.instruction_wf depths default) (.plain encoded) ht hc
    (by simpa [hb] using blocks) (by simpa using hv) (by simp [BrTable.instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices])
/-- Forward preservation projects the shared exact reader certificate. -/
theorem Pending.branch_table {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x0E#u8) :
    code.branch_table st data env ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  apply WP.spec_mono (p.branch_table_reader hbyte)
  intro r effect accepted
  rcases effect accepted with ⟨_, _, _, post⟩
  exact post.after

end Itasca.Wasm2

end

/-! ## Return -/

section

/-!
# `return`

Soundness and completeness of `Wasm2.returnStep`, the `return` arm of the extracted body loop.
`returnStep.prefix` extends a `TypedPrefix` across an accepted return, `returnStep.complete`
accepts when the operands match the function's result vector, and `Pending.return_` shows that the
`return` opcode (`0x0f`) preserves `Pending`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- Returning checks the root function's complete result vector, even within
nested blocks, and erases only the current active stack segment. -/
theorem returnStep.prefix (st : code.BodyState) (env : metadata.Env) (index : U32)
    (results : List wasm_types.ValueType) (cs : List code.Ctrl) (c : code.Ctrl)
    (outer segment : List code.StackType)
    (hctrls : st.core.ctrls.val = cs ++ [c]) (hv : st.core.vals.val = outer ++ segment)
    (hb : c.value_stack_base.val = outer.length)
    (hts : resolve env (.Type index .Results) = some results)
    (C : context) (hC : wf_context C) (inputs : List valtype) (ops : List instr)
    (htyped : TypedPrefix C inputs ops c.polymorphic_base segment)
    (hreturn : C.RETURN = some (.mk_list (results.map Translate.valueType))) :
    returnStep st env index ⦃ r => r.1 = .Ok () → r.2.core.vals.val = outer ∧
      r.2.core.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
      r.2.blocks = st.blocks ∧ r.2.core.pos = st.core.pos ∧
      TypedPrefix C inputs (ops ++ [.RETURN]) true [] ⦄ := by
  have hbase : (Control.base st.core).val = outer.length := by simp [Control.base, hctrls, hb]
  have hpoly : Control.polymorphic st.core = c.polymorphic_base := by simp [Control.polymorphic, hctrls]
  obtain ⟨⟨res, s⟩, hr, hc, hp, rest, hv', _, ht⟩ := WP.spec_imp_exists
    (code.pop_results.realizes st.core env (.Type index .Results) results outer segment hts hv hbase)
  dsimp only at hc hp hv' ht
  cases res with
  | Err e => simp [returnStep, hr]
  | Ok u =>
    obtain ⟨s', hm, hmv, _, hmc, hmp⟩ := WP.spec_imp_exists
      (code.mark_unreachable.spec s cs c (by simpa [hc] using hctrls) (by simp [hv', hb]))
    have hargs := ht rfl _ (Sequence.realizes_default (Control.polymorphic st.core) rest)
    have htyping : TypedPrefix C inputs (ops ++ [.RETURN]) true [] := by
      apply htyped.append hC .RETURN .instr_case_12
      intro out _
      exact ⟨_, by simpa [hpoly] using hargs,
        .instr C .RETURN _ out (.return C _ _ _ hreturn hC .instr_case_12) hC .instr_case_12⟩
    rw [WP.spec_equiv_exists]
    exact ⟨(.Ok (), ⟨s'⟩), by simp [returnStep, hr, hm],
      fun _ => ⟨by simpa [hv', hb] using hmv, hmc, by simp [hmc, hctrls], hmp.trans hp, htyping⟩⟩

/-- Operands that realize the function's results make `returnStep` accept. -/
theorem returnStep.complete (st : code.BodyState) (env : metadata.Env) (index : U32)
    (results : List wasm_types.ValueType) (cs : List code.Ctrl) (c : code.Ctrl)
    (outer segment : List code.StackType) (before : List valtype)
    (hctrls : st.core.ctrls.val = cs ++ [c]) (hv : st.core.vals.val = outer ++ segment)
    (hb : c.value_stack_base.val = outer.length)
    (hts : resolve env (.Type index .Results) = some results)
    (hreal : Sequence.Realizes (Control.polymorphic st.core) segment
      (before ++ results.map Translate.valueType)) :
    ∃ s, returnStep st env index = .ok (.Ok (), s) ∧
      s.core.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
      s.blocks = st.blocks ∧ s.core.pos = st.core.pos ∧ s.core.vals.val = outer := by
  obtain ⟨⟨_, popped⟩, hpop, rfl, hc, hp, rest, hvals, _, _⟩ := WP.spec_imp_exists
    (code.pop_results.complete st.core env (.Type index .Results) results outer segment before
      hts hv (by simp [Control.base, hctrls, hb]) hreal)
  dsimp only at hc hp hvals
  obtain ⟨s, hm, hv', _, hc', hp'⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec popped cs c (by simpa [hc] using hctrls)
      (by simp [hvals, hb]))
  exact ⟨⟨s⟩, by simp [returnStep, hpop, hm], hc', by simp [hc', hctrls],
    hp'.trans hp, by simpa [hvals, hb] using hv'⟩

/-- The `return` opcode (`0x0f`) preserves `Pending` on success. -/
theorem Pending.return_reader {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x0F#u8) :
    returnStep st env index ⦃ r => r.1 = .Ok () →
      r.2.core.vals.val = st.core.vals.val.take p.current.ctrl.value_stack_base.val ∧
      ReaderPost p r.2.core .RETURN true [] ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := id p.opened
  have hC := Frames.enter_wf C (spine.context_wf (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have hreturn : (Frames.enter C p.current.form p.current.ins p.current.outs).RETURN =
      some (.mk_list (p.ft.results.val.map Translate.valueType)) := by
    change C.RETURN = some (.mk_list (p.ft.results.val.map Translate.valueType))
    simpa [bodyContext, EnvTranslation.context] using spine.returns
  apply WP.spec_mono (returnStep.prefix st env index p.ft.results.val
    (p.parents.map Frames.Saved.ctrl) p.current.ctrl outer p.current.vals ctrls vals base
    (by simp [resolve, p.signature]) _ hC _ p.current.ops typed hreturn)
  intro r hr hok
  obtain ⟨hv, hc, hb, hp, ht⟩ := hr hok
  have encoded : Wasm1.At data p.start (.plain .RETURN) r.2.core.pos :=
    .no_immediate p.inbounds hbyte (by simpa [hp] using p.pos) .return_
  refine ⟨by simpa [vals,base] using hv, ?_⟩
  exact p.append_reader_context C outer spine header base r.2.core .RETURN true [] .instr_case_12
    (.plain encoded) ht hc (by simpa [hb] using blocks) (by simpa using hv)
    (encoded.declared _)

/-- Forward preservation projects the shared return-reader certificate. -/
theorem Pending.return_ {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x0F#u8) :
    returnStep st env index ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  apply WP.spec_mono (p.return_reader hbyte)
  intro r effect accepted
  exact (effect accepted).2.after

end Itasca.Wasm2

end
