import Itasca.Handler.EnvCalls
import Itasca.Binary.Wasm1.MemoryTyping
import Itasca.Handler.StackComplete
import Itasca.Binary.Wasm1.EncodingComplete

/-!
# Environment handler completeness

Completeness of the extracted variable, call and memory handlers: when the index is in range,
the immediate decodes and the operand segment realizes the required types, the handler succeeds
with the postcondition `EnvComplete.Post`. Covers the lookup helpers (`code.local_type.complete`,
...), `code.read_local_*`, `code.read_global_*`, `code.read_call`, `code.read_call_indirect`,
`code.read_memory_size`, `code.read_memory_grow`, `code.read_load` and `code.read_store`.
-/

open Aeneas Aeneas.Std

namespace Itasca.EnvComplete

/-- The outcome of a completeness theorem: the handler returns `value`, advances to `next`, keeps
the outer operands, and the remaining operands realize `before` followed by `outputs`, including
unreachable operands represented by `Bot`. -/
def Post {α : Type} (st : code.OpIterState) (outer segment : List code.StackType)
    (before : List valtype) (outputs : List wasm_types.ValueType) (next : Usize) (value : α)
    (r : core.result.Result α error.OpError × code.OpIterState) : Prop :=
  r.1 = .Ok value ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = next ∧
    ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length + outputs.length ∧
      Sequence.Realizes (Control.polymorphic st) rest (before ++ outputs.map Translate.valueType)

end Itasca.EnvComplete

namespace Itasca

/-- `code.local_type` succeeds for an in-range local. -/
theorem code.local_type.complete (ctx : code.Context) (idx : U32) (t : wasm_types.ValueType)
    (hi : idx.val < ctx.locals.val.length) (ht : ctx.locals.val[idx.val] = t) :
    code.local_type ctx idx = .ok (.Ok t) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (code.local_type.spec ctx idx)
  cases r with
  | Ok t' => have heq : t' = t := hp.2.symm.trans ht; simpa [heq] using hr
  | Err e => have := hp.2; omega

/-- `code.global_type` succeeds for an in-range global. -/
theorem code.global_type.complete (env : metadata.Env) (idx : U32) (gt : wasm_types.GlobalType)
    (hi : idx.val < env.global_types.val.length) (ht : env.global_types.val[idx.val] = gt) :
    code.global_type env idx = .ok (.Ok gt) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (code.global_type.spec env idx)
  cases r with
  | Ok gt' => have heq : gt' = gt := hp.2.symm.trans ht; simpa [heq] using hr
  | Err e => have := hp.2; omega

/-- `code.take_local` succeeds when the LEB128 read returns an in-range local index. -/
theorem code.take_local.complete (st : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (idx : U32) (next : Usize) (t : wasm_types.ValueType)
    (hd : reader.read_u32_leb data st.pos = .ok (.Ok (idx, next)))
    (hi : idx.val < ctx.locals.val.length) (ht : ctx.locals.val[idx.val] = t) :
    code.take_local st data ctx = .ok (.Ok (idx, t), { st with pos := next }) := by
  simp [code.take_local, hd, code.local_type.complete ctx idx t hi ht,
    core.result.Result.Insts.CoreOpsTry.branch]

/-- `code.take_global` succeeds when the LEB128 read returns an in-range global index. -/
theorem code.take_global.complete (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (idx : U32) (next : Usize) (gt : wasm_types.GlobalType)
    (hd : reader.read_u32_leb data st.pos = .ok (.Ok (idx, next)))
    (hi : idx.val < env.global_types.val.length) (ht : env.global_types.val[idx.val] = gt) :
    code.take_global st data env = .ok (.Ok (idx, gt), { st with pos := next }) := by
  simp [code.take_global, hd, code.global_type.complete env idx gt hi ht,
    core.result.Result.Insts.CoreOpsTry.branch]

/-- `code.require_memory` succeeds when the environment has a memory. -/
theorem code.require_memory.complete (env : metadata.Env) (h : 0 < env.mem_types.val.length) :
    code.require_memory env = .ok (.Ok ()) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (code.require_memory.spec env)
  cases r with
  | Ok u => cases u; exact hr
  | Err e => simp [hp.2] at h

/-- `code.check_memory_and_alignment` succeeds with a memory and an alignment at most `natural`. -/
theorem code.check_memory_and_alignment.complete (env : metadata.Env) (arg : code.MemArg)
    (natural : U32) (hm : 0 < env.mem_types.val.length) (ha : arg.align.val ≤ natural.val) :
    code.check_memory_and_alignment env arg natural = .ok (.Ok ()) := by
  have hle : ¬ arg.align > natural := by scalar_tac
  simp [code.check_memory_and_alignment, code.require_memory.complete env hm, hle,
    core.result.Result.Insts.CoreOpsTry.branch]

/-- `code.read_local_get` succeeds for an in-range local, pushing its type. -/
theorem code.read_local_get.complete (st : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (idx : U32) (next : Usize) (t : wasm_types.ValueType)
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

/-- `code.read_local_set` succeeds for an in-range local when the segment realizes a stack ending
in its type. -/
theorem code.read_local_set.complete (st : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (idx : U32) (next : Usize) (t : wasm_types.ValueType)
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

/-- `code.read_local_tee` succeeds for an in-range local when the segment realizes a stack ending
in its type, and pushes the type back. -/
theorem code.read_local_tee.complete (st : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (idx : U32) (next : Usize) (t : wasm_types.ValueType)
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

/-- `code.read_global_get` succeeds for an in-range global, pushing its type. -/
theorem code.read_global_get.complete (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (idx : U32) (next : Usize) (gt : wasm_types.GlobalType)
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

/-- `code.read_global_set` succeeds for an in-range mutable global when the segment realizes a
stack ending in its type. -/
theorem code.read_global_set.complete (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (idx : U32) (next : Usize) (gt : wasm_types.GlobalType)
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

end Itasca

open Aeneas Aeneas.Std

namespace Itasca

/-- `code.read_memory_size` succeeds with a memory and a zero reserved byte, pushing an `i32`. -/
theorem code.read_memory_size.complete (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
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

/-- `code.read_memory_grow` succeeds with a memory and a zero reserved byte when the segment
realizes a stack ending in `i32`, and pushes an `i32`. -/
theorem code.read_memory_grow.complete (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
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

/-- `code.read_load` succeeds with a memory and a valid alignment when the segment realizes a stack
ending in the `i32` address, and pushes the loaded type. -/
theorem code.read_load.complete (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (next : Usize) (arg : code.MemArg) (t : wasm_types.ValueType) (natural : U32)
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

/-- `code.read_store` succeeds with a memory and a valid alignment when the segment realizes a
stack ending in the address and stored value. -/
theorem code.read_store.complete (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (next : Usize) (arg : code.MemArg) (t : wasm_types.ValueType) (natural : U32)
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
