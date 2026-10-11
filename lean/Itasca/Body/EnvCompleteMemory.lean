import Itasca.Body.EnvComplete

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
  · exact (Frames.realizes_append_concrete _ segment [.I32] _).mpr ⟨before, hr, rfl⟩

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
  · exact (Frames.realizes_append_concrete _ rest [.I32] _).mpr ⟨before, hrest, rfl⟩

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
  · exact (Frames.realizes_append_concrete _ rest [t] _).mpr ⟨before, hrest, rfl⟩

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
