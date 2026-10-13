import Itasca.Wasm2.Control.FuncType
import Itasca.Wasm2.HandlerAdapters
import Itasca.Wasm2.Prefix
import Itasca.Handler.EnvCalls
import Itasca.Handler.EnvComplete

open Aeneas Aeneas.Std

namespace Itasca

/-- Direct-call acceptance consumes every parameter and supplies every result,
with the function index certified by the independent LEB grammar. -/
theorem code.call.direct_prefix (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (outer segment : List code.StackType)
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
    (env : module.Env) (idx : U32) (next : Usize) (ft : types.FuncType)
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
    (env : module.Env) (ctx : code.Context) (outer segment : List code.StackType)
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
            htablesmall, hget, helem, types.ElemType.value_type,
            core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
            types.ValueType.Insts.CoreCmpPartialEqValueType.eq,
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
                htablesmall, hget, helem, types.ElemType.value_type,
                core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hsmall, hcond,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok popped =>
              obtain ⟨⟨res, s⟩, hs, hout⟩ := WP.spec_imp_exists
                (code.apply_func_type.realizes sc ft outer condrest hvc
                  (by simpa [Control.base, hcc] using hbase))
              cases res with
              | Err e =>
                simp [code.call, code.call_indirect_info, code.take_index, hr, hreadtable, lift,
                  htablesmall, hget, helem, types.ElemType.value_type,
                  core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                  types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hsmall, hcond, hft, hs,
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
                    htablesmall, hget, helem, types.ElemType.value_type,
                    core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                    types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hsmall, hcond, hft, hs,
                    core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                · exact ⟨idx, table, middle, hd, by simpa [Leb128.Post, hp, hpc] using hdtable,
                    hc.trans hcc, code.BodyState.blocks_eq_of_ctrls (hc.trans hcc), _, hv, htyping⟩
          · have hlarge := Nat.le_of_not_gt hi
            simp [code.call, code.call_indirect_info, code.take_index, hr, hreadtable, lift,
              htablesmall, hget, helem, types.ElemType.value_type,
              core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
              types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hlarge,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · have hlarge := Nat.le_of_not_gt htable
        simp [code.call, code.call_indirect_info, code.take_index, hr, hreadtable, lift,
          hlarge, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Independently encoded indices and compatible operands force acceptance. -/
theorem code.call.indirect_complete (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (idx table : U32) (middle next : Usize) (ft : types.FuncType)
    (hd : Leb128.Decoded data st.core.pos idx middle)
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
      htablesmall, hget, helem, types.ElemType.value_type,
      core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hsmall, hcond, hft, ht, hs,
      core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simpa [Control.polymorphic, hcc] using hreal'

end Itasca
