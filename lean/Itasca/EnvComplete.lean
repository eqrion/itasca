import Itasca.EnvCalls
import Itasca.EnvMemory
import Itasca.StackComplete
import Itasca.WasmBinaryComplete

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
  · exact (Frames.realizes_append_concrete _ segment [t] _).mpr ⟨before, hr, rfl⟩

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
  · exact (Frames.realizes_append_concrete _ rest [t] _).mpr ⟨before, hrest, rfl⟩

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
  · exact (Frames.realizes_append_concrete _ segment [gt.valtype] _).mpr ⟨before, hr, rfl⟩

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
