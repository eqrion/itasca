import Itasca.Module.Readers.BasicComplete

/-!
# Completeness of the type readers

Acceptance (`.complete`) of `limits.validate_limits`, `metadata.decode_limits`,
`metadata.decode_mem_type`, `metadata.decode_table_type`, `metadata.decode_global_type`,
`metadata.decode_value_types` and `metadata.decode_func_type` from independent encodings that satisfy
the limit bounds and the profile's allowed types and signature restrictions. Soundness is in
`Module/Readers/Types`.
-/

open Aeneas Aeneas.Std

namespace Itasca
open ModuleBinary

/-- `limits.validate_limits` accepts limits satisfying `LimitsValid`. -/
theorem limits.validate_limits.complete (lim : wasm_types.Limits) (bound : U32)
    (h : LimitsValid lim bound) : limits.validate_limits lim bound = .ok (.Ok ()) := by
  obtain ⟨hmin, hmax⟩ := h
  have hmin' : ¬lim.min > bound := by scalar_tac
  unfold limits.validate_limits
  simp only [hmin', ↓reduceIte]
  cases he : lim.max with
  | none => rfl
  | some maximum =>
      obtain ⟨hlo, hhi⟩ := hmax maximum he
      have hhi' : ¬maximum > bound := by scalar_tac
      have hlo' : ¬lim.min > maximum := by scalar_tac
      simp [hhi', hlo']

/-- `metadata.decode_limits` accepts a `LimitsEncoding` span. -/
theorem metadata.decode_limits.complete (data : Slice U8) (pos : Usize)
    (lim : wasm_types.Limits) (next : Usize) (h : At LimitsEncoding data pos lim next) :
    metadata.decode_limits data pos = .ok (.Ok (lim, next)) := by
  obtain ⟨bytes, he, hs⟩ := h
  cases he with
  | noMax minimum hb =>
      obtain ⟨middle, htag, hbytes⟩ := (show Wasm1.BytesAt data pos ([0#u8] ++ _) next from hs).split
      simp [metadata.decode_limits, htag.read_byte, hbytes.read_u32 minimum hb,
        core.result.Result.Insts.CoreOpsTry.branch]
  | max minimum maximum hlo hhi =>
      obtain ⟨first, htag, hbytes⟩ := (show Wasm1.BytesAt data pos ([1#u8] ++ _) next from hs).split
      obtain ⟨middle, hl, hh⟩ := hbytes.split
      simp [metadata.decode_limits, htag.read_byte, hl.read_u32 minimum hlo,
        hh.read_u32 maximum hhi, core.result.Result.Insts.CoreOpsTry.branch]

/-- `metadata.decode_global_type` accepts a `GlobalTypeEncoding` span whose value type the profile
allows. -/
theorem metadata.decode_global_type.complete (data : Slice U8) (pos : Usize)
    (ty : wasm_types.GlobalType) (next : Usize) (h : At GlobalTypeEncoding data pos ty next)
    (profile : ValidationProfile) (hallowed : ValueTypeAllowed profile ty.valtype) :
    metadata.decode_global_type data pos profile = .ok (.Ok (ty, next)) := by
  obtain ⟨bytes, rfl, hs⟩ := h
  obtain ⟨middle, hvalue, hmut⟩ :=
    (show Wasm1.BytesAt data pos ([valueByte ty.valtype] ++ [mutByte ty.mutability]) next from hs).split
  have hv := metadata.decode_value_type.complete data pos ty.valtype middle ⟨_, rfl, hvalue⟩ profile hallowed
  have hm := hmut.read_byte
  cases ty with
  | mk mutability valtype =>
      cases mutability <;> simp [metadata.decode_global_type, hv, hm, mutByte,
        core.result.Result.Insts.CoreOpsTry.branch]

/-- `metadata.decode_mem_type` accepts a `MemTypeEncoding` span with limits within
`limits.MAX_MEMORY_PAGES`. -/
theorem metadata.decode_mem_type.complete (data : Slice U8) (pos : Usize)
    (ty : wasm_types.MemType) (next : Usize) (h : At MemTypeEncoding data pos ty next)
    (hv : LimitsValid ty.limits limits.MAX_MEMORY_PAGES) :
    metadata.decode_mem_type data pos = .ok (.Ok (ty, next)) := by
  have hr := metadata.decode_limits.complete data pos ty.limits next h
  have hc := limits.validate_limits.complete ty.limits limits.MAX_MEMORY_PAGES hv
  cases ty
  simp [metadata.decode_mem_type, hr, hc, core.result.Result.Insts.CoreOpsTry.branch]

/-- `metadata.decode_table_type` accepts a `TableTypeEncoding` span with limits within
`limits.MAX_TABLE_ELEMS` and an element type the profile allows. -/
theorem metadata.decode_table_type.complete (data : Slice U8) (pos : Usize)
    (ty : wasm_types.TableType) (next : Usize) (h : At TableTypeEncoding data pos ty next)
    (hv : LimitsValid ty.limits limits.MAX_TABLE_ELEMS)
    (profile : ValidationProfile) (hallowed : ElemTypeAllowed profile ty.elem) :
    metadata.decode_table_type data pos profile = .ok (.Ok (ty, next)) := by
  obtain ⟨bytes, ⟨limitBytes, hl, rfl⟩, hs⟩ := h
  obtain ⟨middle, htag, hbytes⟩ := (show Wasm1.BytesAt data pos ([elemByte ty.elem] ++ limitBytes) next from hs).split
  have hr := metadata.decode_limits.complete data middle ty.limits next ⟨_, hl, hbytes⟩
  have hc := limits.validate_limits.complete ty.limits limits.MAX_TABLE_ELEMS hv
  have ht := metadata.decode_elem_type.complete data pos ty.elem middle ⟨_, rfl, htag⟩ profile hallowed
  cases ty
  simp [metadata.decode_table_type, ht, hr, hc, core.result.Result.Insts.CoreOpsTry.branch]


/-- The counted loop accepts an encoded suffix of value types and appends them to the accumulated
`out`, provided the remaining count and capacity fit. -/
theorem metadata.decode_value_types_loop.complete (data : Slice U8) (count : U32)
    (out : alloc.vec.Vec wasm_types.ValueType) (pos : Usize) (i : U32)
    (values : List wasm_types.ValueType) (next : Usize)
    (hbytes : At (Rep ValueTypeEncoding) data pos values next)
    (hcount : i.val + values.length = count.val)
    (hcapacity : out.val.length + values.length ≤ Usize.max)
    (profile : ValidationProfile) (hallowed : ∀ ty ∈ values, ValueTypeAllowed profile ty) :
    ∃ final, metadata.decode_value_types_loop data profile count out pos i = .ok (.Ok (final, next)) ∧
      final.val = out.val ++ values := by
  induction values generalizing out pos i with
  | nil =>
      have hend := hbytes.rep_nil
      subst next
      have hstop : i ≥ count := by simpa using (show count.val ≤ i.val by simpa using hcount.symm.le)
      refine ⟨out, ?_, by simp⟩
      unfold metadata.decode_value_types_loop
      rw [loop]
      simp [metadata.decode_value_types_loop.body, hstop]
  | cons value values ih =>
      obtain ⟨middle, hfirst, hrest⟩ := hbytes.rep_cons
      have hread := metadata.decode_value_type.complete data pos value middle hfirst profile (hallowed value (by simp))
      have hmore : ¬i ≥ count := by scalar_tac
      have hroom : out.val.length < Usize.max := by simp only [List.length_cons] at hcapacity; omega
      obtain ⟨updated, hpush, hout⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out value hroom)
      obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
        (U32.add_spec (x := i) (y := 1#u32) (by scalar_tac))
      obtain ⟨final, hloop, hfinal⟩ := ih updated middle j hrest
        (by simp only [List.length_cons] at hcount; scalar_tac)
        (by simp only [hout, List.length_append, List.length_cons, List.length_nil] at *; omega)
        (fun ty hm => hallowed ty (by simp [hm]))
      refine ⟨final, ?_, by simpa [hout, List.append_assoc] using hfinal⟩
      have hbody : metadata.decode_value_types_loop.body data profile count out pos i =
          .ok (.cont (updated, middle, j)) := by
        simp [metadata.decode_value_types_loop.body, hmore, hread,
          core.result.Result.Insts.CoreOpsTry.branch, hpush, hj]
      unfold metadata.decode_value_types_loop at hloop ⊢
      rw [loop]
      dsimp only
      rw [hbody]
      simpa only [bind_ok] using hloop

/-- `metadata.decode_value_types` accepts a vector span of allowed value types within the length
bound. -/
theorem metadata.decode_value_types.complete (data : Slice U8) (pos : Usize)
    (values : alloc.vec.Vec wasm_types.ValueType) (next : Usize) (limit : Usize) (err : error.OpError)
    (h : At (VecEncoding ValueTypeEncoding) data pos values.val next)
    (hbound : values.val.length ≤ limit.val)
    (profile : ValidationProfile) (hallowed : ∀ ty ∈ values.val, ValueTypeAllowed profile ty) :
    metadata.decode_value_types data pos limit err profile = .ok (.Ok (values, next)) := by
  obtain ⟨count, middle, hcount, hlen, hbytes⟩ := h.vector_split
  have hr := reader.read_u32_leb.complete data pos count middle hlen
  obtain ⟨final, hf, he⟩ := metadata.decode_value_types_loop.complete data count
    (alloc.vec.Vec.new _) middle 0#u32 values.val next hbytes
    (by simpa using hcount.symm) (by simp) profile hallowed
  have heq : final = values := alloc.vec.Vec.ext _ _ (by simpa using he)
  have hfits : ¬ count.val > limit.val := by omega
  simp [metadata.decode_value_types, hr, hf, heq, core.result.Result.Insts.CoreOpsTry.branch,
    lift, hfits]

/-- `metadata.decode_func_type` accepts a `FuncTypeEncoding` span that satisfies the profile's
signature restriction, the signature cap and the allowed value types. -/
theorem metadata.decode_func_type.profile_complete (data : Slice U8) (pos : Usize)
    (ty : wasm_types.FuncType) (next : Usize) (profile : ValidationProfile)
    (h : At FuncTypeEncoding data pos ty next)
    (hprofile : Profile.FuncType profile ty) (hlimits : Profile.FuncTypeWithinLimits ty)
    (hallowed : ∀ t ∈ ty.params.val ++ ty.results.val, ValueTypeAllowed profile t) :
    metadata.decode_func_type data pos profile = .ok (.Ok (ty, next)) := by
  obtain ⟨bytes, ⟨params, results, hp, hr, rfl⟩, hs⟩ := h
  obtain ⟨first, htag, hbytes⟩ :=
    (show Wasm1.BytesAt data pos ([0x60#u8] ++ (params ++ results)) next from hs).split
  obtain ⟨middle, hparams, hresultsBytes⟩ := hbytes.split
  have hp' := metadata.decode_value_types.complete data first ty.params middle
    limits.MAX_MULTI_VALUE_PARAMS error.OpError.TooManyParams ⟨params, hp, hparams⟩ hlimits.1
    profile (fun t ht => hallowed t (List.mem_append_left _ ht))
  have hr' := metadata.decode_value_types.complete data middle ty.results next
    limits.MAX_MULTI_VALUE_RESULTS error.OpError.TooManyResults ⟨results, hr, hresultsBytes⟩ hlimits.2
    profile (fun t ht => hallowed t (List.mem_append_right _ ht))
  cases profile with
  | Wasm1 =>
      have hguard : ¬ alloc.vec.Vec.len ty.results > limits.MAX_RESULTS := by
        simp only [Profile.FuncType] at hprofile
        simp [limits.MAX_RESULTS]; scalar_tac
      cases ty
      simp [metadata.decode_func_type, htag.read_byte, hp', hr', limits.MAX_RESULTS,
        core.result.Result.Insts.CoreOpsTry.branch]
      simpa [Profile.FuncType] using hprofile
  | Wasm2 =>
      cases ty
      simp [metadata.decode_func_type, htag.read_byte, hp', hr',
        core.result.Result.Insts.CoreOpsTry.branch]

end Itasca
