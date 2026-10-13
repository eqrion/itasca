import Itasca.Handler.EnvCalls
import Itasca.Handler.EnvMemory
import Itasca.Handler.StackComplete
import Itasca.Binary.Wasm1.EncodingComplete

open Aeneas Aeneas.Std

namespace Itasca.EnvComplete

/-- Forward execution preserves the concrete outer stack and realizes the
specified output stack, including unreachable operands represented by Bot. -/
def Post {α : Type} (st : code.OpIterState) (outer segment : List code.StackType)
    (before : List valtype) (outputs : List types.ValueType) (next : Usize) (value : α)
    (r : core.result.Result α error.OpError × code.OpIterState) : Prop :=
  r.1 = .Ok value ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = next ∧
    ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length + outputs.length ∧
      Sequence.Realizes (Control.polymorphic st) rest (before ++ outputs.map Translate.valueType)

end Itasca.EnvComplete

namespace Itasca

theorem code.local_type.complete (ctx : code.Context) (idx : U32) (t : types.ValueType)
    (hi : idx.val < ctx.locals.val.length) (ht : ctx.locals.val[idx.val] = t) :
    code.local_type ctx idx = .ok (.Ok t) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (code.local_type.spec ctx idx)
  cases r with
  | Ok t' => have heq : t' = t := hp.2.symm.trans ht; simpa [heq] using hr
  | Err e => have := hp.2; omega

theorem code.global_type.complete (env : module.Env) (idx : U32) (gt : types.GlobalType)
    (hi : idx.val < env.global_types.val.length) (ht : env.global_types.val[idx.val] = gt) :
    code.global_type env idx = .ok (.Ok gt) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (code.global_type.spec env idx)
  cases r with
  | Ok gt' => have heq : gt' = gt := hp.2.symm.trans ht; simpa [heq] using hr
  | Err e => have := hp.2; omega

theorem code.take_local.complete (st : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (idx : U32) (next : Usize) (t : types.ValueType)
    (hd : reader.read_u32_leb data st.pos = .ok (.Ok (idx, next)))
    (hi : idx.val < ctx.locals.val.length) (ht : ctx.locals.val[idx.val] = t) :
    code.take_local st data ctx = .ok (.Ok (idx, t), { st with pos := next }) := by
  simp [code.take_local, hd, code.local_type.complete ctx idx t hi ht,
    core.result.Result.Insts.CoreOpsTry.branch]

theorem code.take_global.complete (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (idx : U32) (next : Usize) (gt : types.GlobalType)
    (hd : reader.read_u32_leb data st.pos = .ok (.Ok (idx, next)))
    (hi : idx.val < env.global_types.val.length) (ht : env.global_types.val[idx.val] = gt) :
    code.take_global st data env = .ok (.Ok (idx, gt), { st with pos := next }) := by
  simp [code.take_global, hd, code.global_type.complete env idx gt hi ht,
    core.result.Result.Insts.CoreOpsTry.branch]

theorem code.require_memory.complete (env : module.Env) (h : 0 < env.mem_types.val.length) :
    code.require_memory env = .ok (.Ok ()) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (code.require_memory.spec env)
  cases r with
  | Ok u => cases u; exact hr
  | Err e => simp [hp.2] at h

theorem code.require_single_result.complete (ts : Slice types.ValueType) (h : ts.val.length ≤ 1) :
    code.require_single_result ts = .ok (.Ok ()) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (code.require_single_result.spec ts)
  cases r with
  | Ok u => cases u; exact hr
  | Err e => have := hp.2; omega

theorem code.check_memory_and_alignment.complete (env : module.Env) (arg : code.MemArg)
    (natural : U32) (hm : 0 < env.mem_types.val.length) (ha : arg.align.val ≤ natural.val) :
    code.check_memory_and_alignment env arg natural = .ok (.Ok ()) := by
  have hle : ¬ arg.align > natural := by scalar_tac
  simp [code.check_memory_and_alignment, code.require_memory.complete env hm, hle,
    core.result.Result.Insts.CoreOpsTry.branch]

theorem code.read_local_get.complete (st : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (idx : U32) (next : Usize) (t : types.ValueType)
    (hd : reader.read_u32_leb data st.pos = .ok (.Ok (idx, next)))
    (hi : idx.val < ctx.locals.val.length) (ht : ctx.locals.val[idx.val] = t)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.vals.val = outer ++ segment) (hsize : st.vals.val.length < Usize.max)
    (hr : Sequence.Realizes (Control.polymorphic st) segment before) :
    code.read_local_get st data ctx ⦃ EnvComplete.Post st outer segment before [t] next idx ⦄ := by
  have htake := code.take_local.complete st data ctx idx next t hd hi ht
  obtain ⟨s, hpush, hvs, hcs, hps⟩ := WP.spec_imp_exists
    (code.push_val.spec {st with pos := next} (.Val t) hsize)
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok idx, s), ?_, rfl, hcs, hps, segment ++ [.Val t], ?_, by simp, ?_⟩
  · simp [code.read_local_get, htake, hpush, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hv, List.append_assoc] using hvs
  · exact (Sequence.realizes_append_concrete _ segment [t] _).mpr ⟨before, hr, rfl⟩

theorem code.read_local_set.complete (st : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (idx : U32) (next : Usize) (t : types.ValueType)
    (hd : reader.read_u32_leb data st.pos = .ok (.Ok (idx, next)))
    (hi : idx.val < ctx.locals.val.length) (ht : ctx.locals.val[idx.val] = t)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.vals.val = outer ++ segment) (hb : (Control.base st).val = outer.length)
    (hr : Sequence.Realizes (Control.polymorphic st) segment (before ++ [Translate.valueType t])) :
    code.read_local_set st data ctx ⦃ EnvComplete.Post st outer segment before [] next idx ⦄ := by
  have htake := code.take_local.complete st data ctx idx next t hd hi ht
  obtain ⟨popped, s, rest, hpop, hcs, hps, hvs, hlen, _, hrest⟩ :=
    code.pop_with_type.complete {st with pos := next} outer segment before t hv hb hr
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok idx, s), ?_, rfl, hcs, hps, rest, hvs, by simpa using hlen, by simpa [Control.polymorphic] using hrest⟩
  simp [code.read_local_set, htake, hpop, core.result.Result.Insts.CoreOpsTry.branch]

theorem code.read_local_tee.complete (st : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (idx : U32) (next : Usize) (t : types.ValueType)
    (hd : reader.read_u32_leb data st.pos = .ok (.Ok (idx, next)))
    (hi : idx.val < ctx.locals.val.length) (ht : ctx.locals.val[idx.val] = t)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.vals.val = outer ++ segment) (hb : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (hr : Sequence.Realizes (Control.polymorphic st) segment (before ++ [Translate.valueType t])) :
    code.read_local_tee st data ctx ⦃ EnvComplete.Post st outer segment before [t] next idx ⦄ := by
  have htake := code.take_local.complete st data ctx idx next t hd hi ht
  obtain ⟨popped, s, rest, hpop, hcs, hps, hvs, hlen, _, hrest⟩ :=
    code.pop_with_type.complete {st with pos := next} outer segment before t hv hb hr
  have hcap : s.vals.val.length < Usize.max := by
    simp only [hvs, hv, List.length_append] at *; omega
  obtain ⟨s', hpush, hv', hc', hp'⟩ := WP.spec_imp_exists (code.push_val.spec s (.Val t) hcap)
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok idx, s'), ?_, rfl, hc'.trans hcs, hp'.trans hps,
    rest ++ [.Val t], ?_, by simpa using Nat.add_le_add_right hlen 1, ?_⟩
  · simp [code.read_local_tee, htake, hpop, hpush, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hvs, List.append_assoc] using hv'
  · exact (Sequence.realizes_append_concrete _ rest [t] _).mpr ⟨before, hrest, rfl⟩

theorem code.read_global_get.complete (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (idx : U32) (next : Usize) (gt : types.GlobalType)
    (hd : reader.read_u32_leb data st.pos = .ok (.Ok (idx, next)))
    (hi : idx.val < env.global_types.val.length) (ht : env.global_types.val[idx.val] = gt)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.vals.val = outer ++ segment) (hsize : st.vals.val.length < Usize.max)
    (hr : Sequence.Realizes (Control.polymorphic st) segment before) :
    code.read_global_get st data env ⦃ EnvComplete.Post st outer segment before [gt.valtype] next idx ⦄ := by
  have htake := code.take_global.complete st data env idx next gt hd hi ht
  obtain ⟨s, hpush, hvs, hcs, hps⟩ := WP.spec_imp_exists
    (code.push_val.spec {st with pos := next} (.Val gt.valtype) hsize)
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok idx, s), ?_, rfl, hcs, hps, segment ++ [.Val gt.valtype], ?_, by simp, ?_⟩
  · simp [code.read_global_get, htake, hpush, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hv, List.append_assoc] using hvs
  · exact (Sequence.realizes_append_concrete _ segment [gt.valtype] _).mpr ⟨before, hr, rfl⟩

theorem code.read_global_set.complete (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (idx : U32) (next : Usize) (gt : types.GlobalType)
    (hd : reader.read_u32_leb data st.pos = .ok (.Ok (idx, next)))
    (hi : idx.val < env.global_types.val.length) (ht : env.global_types.val[idx.val] = gt)
    (hmut : gt.mutability = .Var)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.vals.val = outer ++ segment) (hb : (Control.base st).val = outer.length)
    (hr : Sequence.Realizes (Control.polymorphic st) segment (before ++ [Translate.valueType gt.valtype])) :
    code.read_global_set st data env ⦃ EnvComplete.Post st outer segment before [] next idx ⦄ := by
  have htake := code.take_global.complete st data env idx next gt hd hi ht
  obtain ⟨popped, s, rest, hpop, hcs, hps, hvs, hlen, _, hrest⟩ :=
    code.pop_with_type.complete {st with pos := next} outer segment before gt.valtype hv hb hr
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok idx, s), ?_, rfl, hcs, hps, rest, hvs, by simpa using hlen, by simpa [Control.polymorphic] using hrest⟩
  simp [code.read_global_set, htake, hmut, hpop, core.result.Result.Insts.CoreOpsTry.branch]

end Itasca

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
  · exact (Sequence.realizes_append_concrete _ rest ft.results.val _).mpr ⟨before, hrest, rfl⟩

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
  · apply (Sequence.realizes_append_concrete _ rest ft.results.val _).mpr
    exact ⟨before, by simpa [Control.polymorphic, hcc] using hrest, rfl⟩

end Itasca

open Aeneas Aeneas.Std

namespace Itasca

theorem code.read_memory_size.complete (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (next : Usize) (hz : reader.read_byte data st.pos = .ok (.Ok (0#u8, next)))
    (hm : 0 < env.mem_types.val.length)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.vals.val = outer ++ segment) (hsize : st.vals.val.length < Usize.max)
    (hr : Sequence.Realizes (Control.polymorphic st) segment before) :
    code.read_memory_size st data env ⦃ EnvComplete.Post st outer segment before [.I32] next () ⦄ := by
  have hzero : code.read_reserved_zero st data = .ok (.Ok (), {st with pos := next}) := by
    simp [code.read_reserved_zero, hz, core.result.Result.Insts.CoreOpsTry.branch]
  have hmem := code.require_memory.complete env hm
  obtain ⟨s, hpush, hvs, hcs, hps⟩ := WP.spec_imp_exists
    (code.push_val.spec {st with pos := next} (.Val .I32) hsize)
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok (), s), ?_, rfl, hcs, hps, segment ++ [.Val .I32], ?_, by simp, ?_⟩
  · simp [code.read_memory_size, hzero, hmem, hpush, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hv, List.append_assoc] using hvs
  · exact (Sequence.realizes_append_concrete _ segment [.I32] _).mpr ⟨before, hr, rfl⟩

theorem code.read_memory_grow.complete (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (next : Usize) (hz : reader.read_byte data st.pos = .ok (.Ok (0#u8, next)))
    (hm : 0 < env.mem_types.val.length)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.vals.val = outer ++ segment) (hb : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (hr : Sequence.Realizes (Control.polymorphic st) segment (before ++ [.I32])) :
    code.read_memory_grow st data env ⦃ EnvComplete.Post st outer segment before [.I32] next () ⦄ := by
  have hzero : code.read_reserved_zero st data = .ok (.Ok (), {st with pos := next}) := by
    simp [code.read_reserved_zero, hz, core.result.Result.Insts.CoreOpsTry.branch]
  have hmem := code.require_memory.complete env hm
  obtain ⟨popped, s, rest, hpop, hcs, hps, hvs, hlen, _, hrest⟩ :=
    code.pop_with_type.complete {st with pos := next} outer segment before .I32 hv hb hr
  have hcap : s.vals.val.length < Usize.max := by
    simp only [hvs, hv, List.length_append] at *; omega
  obtain ⟨s', hpush, hv', hc', hp'⟩ := WP.spec_imp_exists (code.push_val.spec s (.Val .I32) hcap)
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok (), s'), ?_, rfl, hc'.trans hcs, hp'.trans hps,
    rest ++ [.Val .I32], ?_, by simpa using Nat.add_le_add_right hlen 1, ?_⟩
  · simp [code.read_memory_grow, hzero, hmem, hpop, hpush, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hvs, List.append_assoc] using hv'
  · exact (Sequence.realizes_append_concrete _ rest [.I32] _).mpr ⟨before, hrest, rfl⟩

theorem code.read_load.complete (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (next : Usize) (arg : code.MemArg) (t : types.ValueType) (natural : U32)
    (hd : code.read_memarg st data = .ok (.Ok arg, {st with pos := next}))
    (hm : 0 < env.mem_types.val.length) (ha : arg.align.val ≤ natural.val)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.vals.val = outer ++ segment) (hb : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (hr : Sequence.Realizes (Control.polymorphic st) segment (before ++ [.I32])) :
    code.read_load st data env t natural ⦃ EnvComplete.Post st outer segment before [t] next arg ⦄ := by
  have hcheck := code.check_memory_and_alignment.complete env arg natural hm ha
  obtain ⟨popped, s, rest, hpop, hcs, hps, hvs, hlen, _, hrest⟩ :=
    code.pop_with_type.complete {st with pos := next} outer segment before .I32 hv hb hr
  have hcap : s.vals.val.length < Usize.max := by
    simp only [hvs, hv, List.length_append] at *; omega
  obtain ⟨s', hpush, hv', hc', hp'⟩ := WP.spec_imp_exists (code.push_val.spec s (.Val t) hcap)
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok arg, s'), ?_, rfl, hc'.trans hcs, hp'.trans hps,
    rest ++ [.Val t], ?_, by simpa using Nat.add_le_add_right hlen 1, ?_⟩
  · simp [code.read_load, hd, hcheck, hpop, hpush, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hvs, List.append_assoc] using hv'
  · exact (Sequence.realizes_append_concrete _ rest [t] _).mpr ⟨before, hrest, rfl⟩

theorem code.read_store.complete (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (next : Usize) (arg : code.MemArg) (t : types.ValueType) (natural : U32)
    (hd : code.read_memarg st data = .ok (.Ok arg, {st with pos := next}))
    (hm : 0 < env.mem_types.val.length) (ha : arg.align.val ≤ natural.val)
    (outer segment : List code.StackType) (before : List valtype)
    (hv : st.vals.val = outer ++ segment) (hb : (Control.base st).val = outer.length)
    (hr : Sequence.Realizes (Control.polymorphic st) segment (before ++ [.I32, Translate.valueType t])) :
    code.read_store st data env t natural ⦃ EnvComplete.Post st outer segment before [] next arg ⦄ := by
  have hcheck := code.check_memory_and_alignment.complete env arg natural hm ha
  obtain ⟨popped, s, rest, hpop, hcs, hps, hvs, hlen, _, hrest⟩ :=
    code.pop_with_type.complete {st with pos := next} outer segment (before ++ [.I32]) t hv hb
      (by simpa [List.append_assoc, Control.polymorphic] using hr)
  obtain ⟨address, s', rest', haddr, hc', hp', hv', hlen', _, hrest'⟩ :=
    code.pop_with_type.complete s outer rest before .I32 hvs
      (by simpa [Control.base, hcs] using hb)
      (by simpa [Control.polymorphic, hcs, Translate.valueType] using hrest)
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok arg, s'), ?_, rfl, hc'.trans hcs, hp'.trans hps,
    rest', hv', by simpa using hlen'.trans hlen, ?_⟩
  · simp [code.read_store, hd, hcheck, hpop, haddr, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [Control.polymorphic, hcs] using hrest'

end Itasca
