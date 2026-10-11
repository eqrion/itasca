import Itasca.Module.ModuleReadersComplete

open Aeneas Aeneas.Std

namespace Itasca
open ModuleBinary

theorem limits.validate_limits.complete (lim : types.Limits) (bound : U32)
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

theorem module.decode_limits.complete (data : Slice U8) (pos : Usize)
    (lim : types.Limits) (next : Usize) (h : At LimitsEncoding data pos lim next) :
    module.decode_limits data pos = .ok (.Ok (lim, next)) := by
  obtain ⟨bytes, he, hs⟩ := h
  cases he with
  | noMax minimum hb =>
      obtain ⟨middle, htag, hbytes⟩ := (show Wasm.BytesAt data pos ([0#u8] ++ _) next from hs).split
      simp [module.decode_limits, htag.read_byte, hbytes.read_u32 minimum hb,
        core.result.Result.Insts.CoreOpsTry.branch]
  | max minimum maximum hlo hhi =>
      obtain ⟨first, htag, hbytes⟩ := (show Wasm.BytesAt data pos ([1#u8] ++ _) next from hs).split
      obtain ⟨middle, hl, hh⟩ := hbytes.split
      simp [module.decode_limits, htag.read_byte, hl.read_u32 minimum hlo,
        hh.read_u32 maximum hhi, core.result.Result.Insts.CoreOpsTry.branch]

theorem module.decode_global_type.complete (data : Slice U8) (pos : Usize)
    (ty : types.GlobalType) (next : Usize) (h : At GlobalTypeEncoding data pos ty next) :
    module.decode_global_type data pos = .ok (.Ok (ty, next)) := by
  obtain ⟨bytes, rfl, hs⟩ := h
  obtain ⟨middle, hvalue, hmut⟩ :=
    (show Wasm.BytesAt data pos ([valueByte ty.valtype] ++ [mutByte ty.mutability]) next from hs).split
  have hv := module.decode_value_type.complete data pos ty.valtype middle ⟨_, rfl, hvalue⟩
  have hm := hmut.read_byte
  cases ty with
  | mk mutability valtype =>
      cases mutability <;> simp [module.decode_global_type, hv, hm, mutByte,
        core.result.Result.Insts.CoreOpsTry.branch]

theorem module.decode_mem_type.complete (data : Slice U8) (pos : Usize)
    (ty : types.MemType) (next : Usize) (h : At MemTypeEncoding data pos ty next)
    (hv : LimitsValid ty.limits limits.MAX_MEMORY_PAGES) :
    module.decode_mem_type data pos = .ok (.Ok (ty, next)) := by
  have hr := module.decode_limits.complete data pos ty.limits next h
  have hc := limits.validate_limits.complete ty.limits limits.MAX_MEMORY_PAGES hv
  cases ty
  simp [module.decode_mem_type, hr, hc, core.result.Result.Insts.CoreOpsTry.branch]

theorem module.decode_table_type.complete (data : Slice U8) (pos : Usize)
    (ty : types.TableType) (next : Usize) (h : At TableTypeEncoding data pos ty next)
    (hv : LimitsValid ty.limits limits.MAX_TABLE_ELEMS) :
    module.decode_table_type data pos = .ok (.Ok (ty, next)) := by
  obtain ⟨bytes, ⟨limitBytes, hl, rfl⟩, hs⟩ := h
  obtain ⟨middle, htag, hbytes⟩ := (show Wasm.BytesAt data pos ([0x70#u8] ++ limitBytes) next from hs).split
  have hr := module.decode_limits.complete data middle ty.limits next ⟨_, hl, hbytes⟩
  have hc := limits.validate_limits.complete ty.limits limits.MAX_TABLE_ELEMS hv
  cases ty with
  | mk lim elem =>
      cases elem
      simp [module.decode_table_type, htag.read_byte, hr, hc, core.result.Result.Insts.CoreOpsTry.branch]


/-- The counted reader accepts an independently encoded suffix while preserving
an arbitrary already accumulated prefix. -/
theorem module.decode_value_types_loop0.complete (data : Slice U8) (count : U32)
    (out : alloc.vec.Vec types.ValueType) (pos : Usize) (i : U32)
    (values : List types.ValueType) (next : Usize)
    (hbytes : At (Rep ValueTypeEncoding) data pos values next)
    (hcount : i.val + values.length = count.val)
    (hcapacity : out.val.length + values.length ≤ Usize.max) :
    ∃ final, module.decode_value_types_loop0 data count out pos i = .ok (.Ok (final, next)) ∧
      final.val = out.val ++ values := by
  induction values generalizing out pos i with
  | nil =>
      have hend := hbytes.rep_nil
      subst next
      have hstop : i ≥ count := by simpa using (show count.val ≤ i.val by simpa using hcount.symm.le)
      refine ⟨out, ?_, by simp⟩
      unfold module.decode_value_types_loop0
      rw [loop]
      simp [module.decode_value_types_loop0.body, hstop]
  | cons value values ih =>
      obtain ⟨middle, hfirst, hrest⟩ := hbytes.rep_cons
      have hread := module.decode_value_type.complete data pos value middle hfirst
      have hmore : ¬i ≥ count := by scalar_tac
      have hroom : out.val.length < Usize.max := by simp only [List.length_cons] at hcapacity; omega
      obtain ⟨updated, hpush, hout⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out value hroom)
      obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
        (U32.add_spec (x := i) (y := 1#u32) (by scalar_tac))
      obtain ⟨final, hloop, hfinal⟩ := ih updated middle j hrest
        (by simp only [List.length_cons] at hcount; scalar_tac)
        (by simp only [hout, List.length_append, List.length_cons, List.length_nil] at *; omega)
      refine ⟨final, ?_, by simpa [hout, List.append_assoc] using hfinal⟩
      have hbody : module.decode_value_types_loop0.body data count out pos i =
          .ok (.cont (updated, middle, j)) := by
        simp [module.decode_value_types_loop0.body, hmore, hread,
          core.result.Result.Insts.CoreOpsTry.branch, hpush, hj]
      unfold module.decode_value_types_loop0 at hloop ⊢
      rw [loop]
      dsimp only
      rw [hbody]
      simpa only [bind_ok] using hloop

theorem module.decode_value_types.complete (data : Slice U8) (pos : Usize)
    (values : alloc.vec.Vec types.ValueType) (next : Usize)
    (h : At (VecEncoding ValueTypeEncoding) data pos values.val next) :
    module.decode_value_types data pos none = .ok (.Ok (values, next)) := by
  obtain ⟨count, middle, hcount, hlen, hbytes⟩ := h.vector_split
  have hr := reader.read_u32_leb.complete data pos count middle hlen
  obtain ⟨final, hf, he⟩ := module.decode_value_types_loop0.complete data count
    (alloc.vec.Vec.new _) middle 0#u32 values.val next hbytes
    (by simpa using hcount.symm) (by simp)
  have heq : final = values := alloc.vec.Vec.ext _ _ (by simpa using he)
  simp [module.decode_value_types, hr, hf, heq, core.result.Result.Insts.CoreOpsTry.branch]

theorem module.decode_value_types.profile_complete (data : Slice U8) (pos : Usize)
    (values : alloc.vec.Vec types.ValueType) (next : Usize)
    (bound : Option (Usize × error.OpError))
    (h : At (VecEncoding ValueTypeEncoding) data pos values.val next)
    (hbound : ∀ limit err, bound = some (limit, err) → values.val.length ≤ limit.val) :
    module.decode_value_types data pos bound = .ok (.Ok (values, next)) := by
  cases bound with
  | none => exact module.decode_value_types.complete data pos values next h
  | some pair =>
      obtain ⟨limit, err⟩ := pair
      obtain ⟨count, middle, hcount, hlen, hbytes⟩ := h.vector_split
      have hr := reader.read_u32_leb.complete data pos count middle hlen
      obtain ⟨final, hf, he⟩ := module.decode_value_types_loop0.complete data count
        (alloc.vec.Vec.new _) middle 0#u32 values.val next hbytes
        (by simpa using hcount.symm) (by simp)
      have heq : final = values := alloc.vec.Vec.ext _ _ (by simpa using he)
      have hfits : ¬ count.val > limit.val := by
        have := hbound limit err rfl
        omega
      simp [module.decode_value_types, hr, hf, heq, core.result.Result.Insts.CoreOpsTry.branch,
        lift, hfits, module.decode_value_types_loop1.eq_loop0]

theorem module.decode_func_type.complete (data : Slice U8) (pos : Usize)
    (ty : types.FuncType) (next : Usize) (h : At FuncTypeEncoding data pos ty next)
    (hresults : ty.results.val.length ≤ 1) :
    module.decode_func_type data pos .Wasm1 = .ok (.Ok (ty, next)) := by
  obtain ⟨bytes, ⟨params, results, hp, hr, rfl⟩, hs⟩ := h
  obtain ⟨first, htag, hbytes⟩ :=
    (show Wasm.BytesAt data pos ([0x60#u8] ++ (params ++ results)) next from hs).split
  obtain ⟨middle, hparams, hresultsBytes⟩ := hbytes.split
  have hp' := module.decode_value_types.complete data first ty.params middle ⟨params, hp, hparams⟩
  have hr' := module.decode_value_types.complete data middle ty.results next ⟨results, hr, hresultsBytes⟩
  have hguard : ¬ alloc.vec.Vec.len ty.results > limits.MAX_RESULTS := by
    simp [limits.MAX_RESULTS]; scalar_tac
  cases ty
  simp [module.decode_func_type, htag.read_byte, hp', hr', limits.MAX_RESULTS, hresults,
    core.result.Result.Insts.CoreOpsTry.branch]

theorem module.decode_func_type.profile_complete (data : Slice U8) (pos : Usize)
    (ty : types.FuncType) (next : Usize) (profile : ValidationProfile)
    (h : At FuncTypeEncoding data pos ty next)
    (hprofile : Profile.FuncType profile ty) (hlimits : Profile.FuncTypeWithinLimits profile ty) :
    module.decode_func_type data pos profile = .ok (.Ok (ty, next)) := by
  cases profile with
  | Wasm1 => exact module.decode_func_type.complete data pos ty next h hprofile
  | MultiValue =>
      obtain ⟨bytes, ⟨params, results, hp, hr, rfl⟩, hs⟩ := h
      obtain ⟨first, htag, hbytes⟩ :=
        (show Wasm.BytesAt data pos ([0x60#u8] ++ (params ++ results)) next from hs).split
      obtain ⟨middle, hparams, hresultsBytes⟩ := hbytes.split
      have hp' := module.decode_value_types.profile_complete data first ty.params middle
        (some (multi_value.MAX_PARAMS, error.OpError.TooManyParams)) ⟨params, hp, hparams⟩
        (by intro limit err he; cases he; exact hlimits.1)
      have hr' := module.decode_value_types.profile_complete data middle ty.results next
        (some (multi_value.MAX_RESULTS, error.OpError.TooManyResults)) ⟨results, hr, hresultsBytes⟩
        (by intro limit err he; cases he; exact hlimits.2)
      cases ty
      simp [module.decode_func_type, htag.read_byte, hp', hr',
        core.result.Result.Insts.CoreOpsTry.branch]

end Itasca
