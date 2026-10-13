import Itasca.Handler.EnvComplete

open Aeneas Aeneas.Std

namespace Itasca

/-- Direct calls use the stored function signature cache, exactly as the public validator does. -/
theorem code.read_call.complete (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (idx : U32) (next : Usize) (ft : types.FuncType)
    (hd : reader.read_u32_leb data st.pos = .ok (.Ok (idx, next)))
    (hi : idx.val < env.func_types.val.length) (ht : env.func_types.val[idx.val] = ft)
    (harity : ft.results.val.length ≤ 1)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.vals.val = outer ++ segment) (hb : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (hr : Sequence.Realizes (Control.polymorphic st) segment
      (before ++ ft.params.val.map Translate.valueType)) :
    code.read_call st data env ⦃ EnvComplete.Post st outer segment before ft.results.val next idx ⦄ := by
  have htake : code.take_index st data = .ok (.Ok idx, {st with pos := next}) := by
    simp [code.take_index, hd, core.result.Result.Insts.CoreOpsTry.branch]
  have hix : (UScalar.cast .Usize idx).val < env.func_types.val.length := by simpa using hi
  obtain ⟨ft', hft, hfteq⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec env.func_types (UScalar.cast .Usize idx) hix)
  have heq : ft' = ft := by simpa [ht] using hfteq
  rw [heq] at hft
  have hsmall := Nat.not_le_of_gt hi
  have hreq := code.require_single_result.complete (alloc.vec.Vec.deref ft.results)
    (by simpa [alloc.vec.Vec.deref] using harity)
  obtain ⟨⟨_, s⟩, hpop, rfl, hcs, hps, rest, hvs, hlen, hrest⟩ := WP.spec_imp_exists
    (code.pop_types.complete {st with pos := next} outer segment before
      (alloc.vec.Vec.deref ft.params) hv hb
      (by simpa [alloc.vec.Vec.deref, Control.polymorphic] using hr))
  dsimp only at hcs hps hvs hlen hrest
  have hcap : s.vals.val.length + (alloc.vec.Vec.deref ft.results).val.length ≤ Usize.max := by
    have hcap' : s.vals.val.length + ft.results.val.length ≤ Usize.max := by
      simp only [hvs, hv, List.length_append] at *; omega
    simpa [alloc.vec.Vec.deref] using hcap'
  obtain ⟨s', hpush, hv', hc', hp'⟩ := WP.spec_imp_exists
    (code.push_types.spec s (alloc.vec.Vec.deref ft.results) hcap)
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok idx, s'), ?_, rfl, hc'.trans hcs, hp'.trans hps,
    rest ++ ft.results.val.map code.StackType.Val, ?_, ?_, ?_⟩
  · simp [code.read_call, htake, lift, hsmall, hft, hreq, hpop, hpush,
      core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hvs, List.append_assoc, alloc.vec.Vec.deref] using hv'
  · simpa using Nat.add_le_add_right hlen ft.results.val.length
  · exact (Frames.realizes_append_concrete _ rest ft.results.val _).mpr ⟨before, hrest, rfl⟩

/-- Indirect calls consume the selector before the arguments and use env.types. -/
theorem code.read_call_indirect.complete (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (idx : U32) (middle next : Usize) (ft : types.FuncType)
    (hd : reader.read_u32_leb data st.pos = .ok (.Ok (idx, middle)))
    (hz : reader.read_byte data middle = .ok (.Ok (0#u8, next)))
    (htable : 0 < env.table_types.val.length)
    (hfun : env.table_types.val[0].elem = .FuncRef)
    (hi : idx.val < env.types.val.length) (ht : env.types.val[idx.val] = ft)
    (harity : ft.results.val.length ≤ 1)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.vals.val = outer ++ segment) (hb : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (hr : Sequence.Realizes (Control.polymorphic st) segment
      (before ++ (ft.params.val.map Translate.valueType ++ [.I32]))) :
    code.read_call_indirect st data env ⦃ EnvComplete.Post st outer segment before ft.results.val next idx ⦄ := by
  have htake : code.take_index st data = .ok (.Ok idx, {st with pos := middle}) := by
    simp [code.take_index, hd, core.result.Result.Insts.CoreOpsTry.branch]
  have hzero : code.read_reserved_zero {st with pos := middle} data =
      .ok (.Ok (), {st with pos := next}) := by
    simp [code.read_reserved_zero, hz, core.result.Result.Insts.CoreOpsTry.branch]
  have hnonempty : env.table_types.val ≠ [] := by simpa using List.ne_nil_of_length_pos htable
  obtain ⟨tt, hget, hgeteq⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec env.table_types 0#usize (by simpa using htable))
  have helem : tt.elem = .FuncRef := by simpa [hgeteq] using hfun
  have hix : (UScalar.cast .Usize idx).val < env.types.val.length := by simpa using hi
  obtain ⟨ft', hft, hfteq⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec env.types (UScalar.cast .Usize idx) hix)
  have heq : ft' = ft := by simpa [ht] using hfteq
  rw [heq] at hft
  have hsmall := Nat.not_le_of_gt hi
  have hreq := code.require_single_result.complete (alloc.vec.Vec.deref ft.results)
    (by simpa [alloc.vec.Vec.deref] using harity)
  obtain ⟨popped, sc, condrest, hcond, hcc, hpc, hvc, hlc, _, hcondrest⟩ :=
    code.pop_with_type.complete {st with pos := next} outer segment
      (before ++ ft.params.val.map Translate.valueType) .I32 hv hb
      (by simpa [List.append_assoc, Translate.valueType, Control.polymorphic] using hr)
  obtain ⟨⟨_, s⟩, hpop, rfl, hcs, hps, rest, hvs, hlen, hrest⟩ := WP.spec_imp_exists
    (code.pop_types.complete sc outer condrest before (alloc.vec.Vec.deref ft.params) hvc
      (by simpa [Control.base, hcc] using hb)
      (by simpa [Control.polymorphic, hcc, alloc.vec.Vec.deref] using hcondrest))
  dsimp only at hcs hps hvs hlen hrest
  have hcap : s.vals.val.length + (alloc.vec.Vec.deref ft.results).val.length ≤ Usize.max := by
    have hcap' : s.vals.val.length + ft.results.val.length ≤ Usize.max := by
      simp only [hvs, hv, List.length_append] at *; omega
    simpa [alloc.vec.Vec.deref] using hcap'
  obtain ⟨s', hpush, hv', hc', hp'⟩ := WP.spec_imp_exists
    (code.push_types.spec s (alloc.vec.Vec.deref ft.results) hcap)
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok idx, s'), ?_, rfl, hc'.trans (hcs.trans hcc), hp'.trans (hps.trans hpc),
    rest ++ ft.results.val.map code.StackType.Val, ?_, ?_, ?_⟩
  · simp [code.read_call_indirect, hget, helem, types.ElemType.value_type,
      core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      types.ValueType.Insts.CoreCmpPartialEqValueType.eq, htake, hzero, alloc.vec.Vec.is_empty, hnonempty,
      lift, hsmall, hft, hreq, hcond, hpop, hpush, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hvs, List.append_assoc, alloc.vec.Vec.deref] using hv'
  · simpa using Nat.add_le_add_right (hlen.trans hlc) ft.results.val.length
  · apply (Frames.realizes_append_concrete _ rest ft.results.val _).mpr
    exact ⟨before, by simpa [Control.polymorphic, hcc] using hrest, rfl⟩

end Itasca
