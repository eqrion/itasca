import Itasca.MultiValue.Calls
import Itasca.MultiValue.HandlerAdapters
import Itasca.MultiValue.Prefix
import Itasca.Body.EnvCalls
import Itasca.Body.EnvCompleteCalls

open Aeneas Aeneas.Std

namespace Itasca

/-- Direct-call acceptance consumes every parameter and supplies every result,
with the function index certified by the independent LEB grammar. -/
theorem multi_value.call.direct_prefix (st : multi_value.State) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.core.vals.val = outer ++ segment)
    (hbase : (Control.base st.core).val = outer.length)
    (C : context) (hC : EnvTranslation.Matches env ctx C) (inputs : List valtype) (ops : List instr)
    (htyped : MultiValue.TypedPrefix C inputs ops (Control.polymorphic st.core) segment) :
    multi_value.call st data env false ⦃ r => r.1 = .Ok () →
      ∃ idx, Leb128.Decoded data st.core.pos idx r.2.core.pos ∧
      r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧
      ∃ rest, r.2.core.vals.val = outer ++ rest ∧
        MultiValue.TypedPrefix C inputs (ops ++ [.CALL (.mk_uN idx.val)])
          (Control.polymorphic st.core) rest ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  cases r with
  | Err e => simp [multi_value.call.eq_core, MultiValue.callCore, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨idx, next⟩ := pair
    by_cases hi : idx.val < env.func_types.val.length
    · have hix : (UScalar.cast .Usize idx).val < env.func_types.val.length := by simpa using hi
      obtain ⟨ft, hft, heq⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec env.func_types (UScalar.cast .Usize idx) hix)
      have htype : env.func_types.val[idx.val] = ft := by simpa using heq.symm
      have hsmall := Nat.not_le_of_gt hi
      obtain ⟨⟨res, s⟩, hs, hout⟩ := WP.spec_imp_exists
        (multi_value.apply_func_type.realizes { st.core with pos := next } ft outer segment hvals hbase)
      cases res with
      | Err e => simp [multi_value.call.eq_core, MultiValue.callCore, hr, lift, hsmall, hft, htype, hs,
          core.result.Result.Insts.CoreOpsTry.branch]
      | Ok u =>
        obtain ⟨hc, hp, _, _, rest, hv, _, ht⟩ := hout rfl
        dsimp only at hc hp hv ht
        have ht' : ∀ ts, Sequence.Realizes (Control.polymorphic st.core) rest ts →
            Sequence.Realizes (Control.polymorphic st.core) segment
              (ts ++ ft.params.val.map Translate.valueType) := ht
        have htyping := (MultiValue.ResumePrefix.after_pop htyped ht').finish hC.wf
          (.CALL (.mk_uN idx.val)) ft.results.val (.instr_case_10 _ (EnvTranslation.index_wf idx))
          (hC.call idx ft hi htype)
        rw [WP.spec_equiv_exists]
        refine ⟨(.Ok (), ⟨s⟩), ?_, fun _ => ?_⟩
        · simp [multi_value.call.eq_core, MultiValue.callCore, hr, lift, hsmall, hft, htype, hs,
            core.result.Result.Insts.CoreOpsTry.branch]
        · exact ⟨idx, by simpa [hp, Leb128.Post] using hd, hc, multi_value.State.blocks_eq_of_ctrls hc, _, hv, htyping⟩
    · have hlarge := Nat.le_of_not_gt hi
      simp [multi_value.call.eq_core, MultiValue.callCore, hr, lift, hlarge, core.result.Result.Insts.CoreOpsTry.branch]

/-- Direct calls accept independently encoded, in-range function indices and
compatible operands within the explicit signature and operand capacity limits. -/
theorem multi_value.call.direct_complete (st : multi_value.State) (data : Slice U8)
    (env : module.Env) (idx : U32) (next : Usize) (ft : types.FuncType)
    (hd : Leb128.Decoded data st.core.pos idx next)
    (hi : idx.val < env.func_types.val.length) (ht : env.func_types.val[idx.val] = ft)
    (hp : ft.params.val.length ≤ 1000) (hr : ft.results.val.length ≤ 1000)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.core.vals.val = outer ++ segment) (hb : (Control.base st.core).val = outer.length)
    (hcap : st.core.vals.val.length + ft.results.val.length ≤ Usize.max)
    (hreal : Sequence.Realizes (Control.polymorphic st.core) segment
      (before ++ ft.params.val.map Translate.valueType)) :
    multi_value.call st data env false ⦃ r => r.1 = .Ok () ∧
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
    (multi_value.apply_func_type.complete { st.core with pos := next } ft outer segment before
      hp hr hv hb hcap hreal)
  have hsmall := Nat.not_le_of_gt hi
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok (), ⟨s⟩), ?_, rfl, hc, multi_value.State.blocks_eq_of_ctrls hc, hpos, rest, hvs, hlen, hreal'⟩
  simp [multi_value.call.eq_core, MultiValue.callCore, hread, lift, hsmall, hft, ht, hs,
    core.result.Result.Insts.CoreOpsTry.branch]

/-- Indirect calls retain the table-zero byte and consume the selector before
all function parameters; result arity is unrestricted by the proof. -/
theorem multi_value.call.indirect_prefix (st : multi_value.State) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.core.vals.val = outer ++ segment)
    (hbase : (Control.base st.core).val = outer.length)
    (C : context) (hC : EnvTranslation.Matches env ctx C) (inputs : List valtype) (ops : List instr)
    (htyped : MultiValue.TypedPrefix C inputs ops (Control.polymorphic st.core) segment) :
    multi_value.call st data env true ⦃ r => r.1 = .Ok () →
      ∃ idx middle, Leb128.Decoded data st.core.pos idx middle ∧
      (∃ hm : middle.val < data.length, data.val[middle.val] = 0#u8 ∧
        r.2.core.pos.val = middle.val + 1) ∧
      r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧
      ∃ rest, r.2.core.vals.val = outer ++ rest ∧
        MultiValue.TypedPrefix C inputs (ops ++ [.CALL_INDIRECT (.mk_uN 0) (.mk_uN idx.val)])
          (Control.polymorphic st.core) rest ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  cases r with
  | Err e => simp [multi_value.call.eq_core, MultiValue.callCore, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨idx, middle⟩ := pair
    by_cases hm : middle.val < data.length
    · obtain ⟨_, hz, next, rfl, hn⟩ := WP.spec_imp_exists (reader.read_byte.spec data middle hm)
      by_cases hzbyte : data.val[middle.val] = 0#u8
      · by_cases htable : env.table_types.val = []
        · simp [multi_value.call.eq_core, MultiValue.callCore, hr, hz, hzbyte, lift, alloc.vec.Vec.is_empty, htable,
            core.result.Result.Insts.CoreOpsTry.branch]
        · by_cases hi : idx.val < env.types.val.length
          · have hix : (UScalar.cast .Usize idx).val < env.types.val.length := by simpa using hi
            obtain ⟨ft, hft, heq⟩ := WP.spec_imp_exists
              (alloc.vec.Vec.index_usize_spec env.types (UScalar.cast .Usize idx) hix)
            have htype : env.types.val[idx.val] = ft := by simpa using heq.symm
            have hsmall := Nat.not_le_of_gt hi
            obtain ⟨⟨rc, sc⟩, hcond, hcc, hpc, condrest, hvc, _, htc⟩ := WP.spec_imp_exists
              (code.pop_with_type.realizes { st.core with pos := next } outer segment .I32 hvals hbase)
            dsimp only at hcc hpc hvc htc
            cases rc with
            | Err e => simp [multi_value.call.eq_core, MultiValue.callCore, hr, hz, hzbyte, alloc.vec.Vec.is_empty,
                htable, lift, hsmall, hcond, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok popped =>
              obtain ⟨⟨res, s⟩, hs, hout⟩ := WP.spec_imp_exists
                (multi_value.apply_func_type.realizes sc ft outer condrest hvc
                  (by simpa [Control.base, hcc] using hbase))
              cases res with
              | Err e => simp [multi_value.call.eq_core, MultiValue.callCore, hr, hz, hzbyte, alloc.vec.Vec.is_empty,
                  htable, lift, hsmall, hcond, hft, htype, hs, core.result.Result.Insts.CoreOpsTry.branch]
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
                have htyping := (MultiValue.ResumePrefix.after_pop htyped htransfer).finish hC.wf
                  (.CALL_INDIRECT (.mk_uN 0) (.mk_uN idx.val)) ft.results.val
                  (.instr_case_11 _ _ (EnvTranslation.index_wf 0#u32) (EnvTranslation.index_wf idx))
                  (hC.call_indirect idx ft hi htype (List.length_pos_iff.mpr htable))
                rw [WP.spec_equiv_exists]
                refine ⟨(.Ok (), ⟨s⟩), ?_, fun _ => ?_⟩
                · simp [multi_value.call.eq_core, MultiValue.callCore, hr, hz, hzbyte, alloc.vec.Vec.is_empty,
                    htable, lift, hsmall, hcond, hft, htype, hs, core.result.Result.Insts.CoreOpsTry.branch]
                · exact ⟨idx, middle, hd, ⟨hm, hzbyte, by simpa [hp, hpc] using hn⟩,
                    hc.trans hcc, multi_value.State.blocks_eq_of_ctrls (hc.trans hcc), _, hv, htyping⟩
          · have hlarge := Nat.le_of_not_gt hi
            simp [multi_value.call.eq_core, MultiValue.callCore, hr, hz, hzbyte, lift, alloc.vec.Vec.is_empty, htable,
              lift, hlarge, core.result.Result.Insts.CoreOpsTry.branch]
      · have hzval : data.val[middle.val].val ≠ 0 := fun h => hzbyte (UScalar.eq_of_val_eq h)
        simp [multi_value.call.eq_core, MultiValue.callCore, hr, hz, hzval, lift, core.result.Result.Insts.CoreOpsTry.branch]
    · simp [multi_value.call.eq_core, MultiValue.callCore, hr, lift, reader.read_byte.eof data middle (by omega),
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Independent indirect-call bytes and compatible operands force acceptance. -/
theorem multi_value.call.indirect_complete (st : multi_value.State) (data : Slice U8)
    (env : module.Env) (idx : U32) (middle next : Usize) (ft : types.FuncType)
    (hd : Leb128.Decoded data st.core.pos idx middle)
    (hm : middle.val < data.length) (hzbyte : data.val[middle.val] = 0#u8)
    (hn : next.val = middle.val + 1)
    (htable : 0 < env.table_types.val.length)
    (hi : idx.val < env.types.val.length) (ht : env.types.val[idx.val] = ft)
    (hp : ft.params.val.length ≤ 1000) (hr : ft.results.val.length ≤ 1000)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.core.vals.val = outer ++ segment) (hb : (Control.base st.core).val = outer.length)
    (hcap : st.core.vals.val.length + ft.results.val.length ≤ Usize.max)
    (hreal : Sequence.Realizes (Control.polymorphic st.core) segment
      (before ++ (ft.params.val.map Translate.valueType ++ [.I32]))) :
    multi_value.call st data env true ⦃ r => r.1 = .Ok () ∧
      r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧ r.2.core.pos = next ∧
      ∃ rest, r.2.core.vals.val = outer ++ rest ∧
        rest.length ≤ segment.length + ft.results.val.length ∧
        Sequence.Realizes (Control.polymorphic st.core) rest
          (before ++ ft.results.val.map Translate.valueType) ⦄ := by
  have hread := reader.read_u32_leb.complete data st.core.pos idx middle hd
  obtain ⟨_, hz, next', rfl, hn'⟩ := WP.spec_imp_exists (reader.read_byte.spec data middle hm)
  have he : next' = next := UScalar.eq_of_val_eq (by omega)
  subst next'
  have hnonempty := List.ne_nil_of_length_pos htable
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
    (multi_value.apply_func_type.complete sc ft outer condrest before hp hr hvc
      (by simpa [Control.base, hcc] using hb) hcap'
      (by simpa [Control.polymorphic, hcc] using htc))
  have hsmall := Nat.not_le_of_gt hi
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok (), ⟨s⟩), ?_, rfl, hc.trans hcc, multi_value.State.blocks_eq_of_ctrls (hc.trans hcc), hpos.trans hpc,
    rest, hvs, by omega, ?_⟩
  · simp [multi_value.call.eq_core, MultiValue.callCore, hread, hz, hzbyte, alloc.vec.Vec.is_empty,
      hnonempty, lift, hsmall, hcond, hft, ht, hs, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [Control.polymorphic, hcc] using hreal'

end Itasca
