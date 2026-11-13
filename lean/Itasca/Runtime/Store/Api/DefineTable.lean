import Itasca.Runtime.Representation.StoreCapacity
import Itasca.Runtime.Platform.Laws
import Itasca.Runtime.Store.Invariant.ValueShape

/-!
Sections, each formerly its own module: Grow, Write, Define, DefineMemory, DefineTable.
-/

/-! ## Grow -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

@[step] theorem within_spec (current additional limit : Usize) :
    runtime.store.within current additional limit ⦃ answer =>
      answer = decide (current.val + additional.val ≤ limit.val) ⦄ := by
  unfold runtime.store.within
  step as ⟨total, ht⟩
  cases total with
  | none => simp_all; scalar_tac
  | some total => simp_all

@[step] theorem table_grow_loop (before : alloc.vec.Vec U64) (n : U64)
    (old : Usize) (value : U64) (hi : old.val = before.length)
    (hsize : before.length ≤ n.val) (hmax : n.val ≤ Usize.max) :
    runtime.store.Store.grow_table_index_loop value n before old ⦃ after =>
      after.val = before.val ++ List.replicate (n.val - before.length) value ⦄ := by
  have hcast : (UScalar.cast .Usize n).val = n.val := by
    rw [UScalar.cast_val_eq, Nat.mod_eq_of_lt]
    have hm : Usize.max = 2^Usize.numBits-1 := by simp [Usize.max]
    simp only [UScalarTy.numBits, Usize.numBits] at hm ⊢
    have hp : 0 < 2^System.Platform.numBits := Nat.two_pow_pos _
    omega
  unfold runtime.store.Store.grow_table_index_loop
  apply loop.spec_decr_nat (fun pair => n.val - pair.2.val)
    (fun pair => pair.2.val = pair.1.length ∧ pair.1.length ≤ n.val ∧
      pair.1.val ++ List.replicate (n.val - pair.1.length) value =
        before.val ++ List.replicate (n.val - before.length) value)
  · intro pair hinv
    rcases pair with ⟨items, pos⟩
    rcases hinv with ⟨hpos, hlen, hbytes⟩
    unfold runtime.store.Store.grow_table_index_loop.body
    dsimp only at hpos hlen hbytes
    simp [lift]
    split
    · rename_i hmore
      have hlt : items.length < n.val := by scalar_tac
      have hpush : items.length < Usize.max := by omega
      step as ⟨after, hafter⟩
      step as ⟨next, hnext⟩
      have hlen' : after.length = items.length + 1 := by simp [hafter]
      simp only [alloc.vec.Vec.length] at *
      refine ⟨?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · rw [hafter, List.append_assoc]
        have heq : n.val - items.val.length = (n.val - after.val.length) + 1 := by omega
        rw [heq] at hbytes
        simpa [List.replicate_succ, hafter] using hbytes
      · omega
    · rename_i hstop
      have heq : items.length = n.val := by scalar_tac
      simpa [WP.spec_ok, heq] using hbytes
  · exact ⟨hi, hsize, rfl⟩

def TableGrowth {M : Type} (s : runtime.store.Store M) (index : Usize)
    (delta : U32) (value : U64) (result : U32 × runtime.store.Store M) : Prop :=
  (result.1 = core.num.U32.MAX ∧ result.2 = s) ∨
  ∃ old : runtime.store.TableInst, ∃ elements : alloc.vec.Vec U64, ∃ count : Usize,
    s.tables.val[index.val]? = some old ∧
    elements.val = old.elements.val ++ List.replicate delta.val value ∧
    old.elements.length + delta.val ≤ U32.max ∧
    count.val = s.table_elements.val + delta.val ∧
    count.val ≤ s.limits.max_table_elements.val ∧
    old.elements.length + delta.val ≤ (core.option.Option.unwrap_or old.maximum core.num.U32.MAX).val ∧
    result = (UScalar.cast .U32 (alloc.vec.Vec.len old.elements),
      {s with tables := s.tables.set index {old with elements := elements}, table_elements := count})

theorem table_grow_effect {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (s : runtime.store.Store M) (index : Usize) (delta : U32) (value : U64)
    (hindex : index.val < s.tables.length)
    (hsizes : ∀ t ∈ s.tables.val, t.elements.length ≤ U32.max) :
    runtime.store.Store.grow_table_index ops allocator s index delta value ⦃ result => TableGrowth s index delta value result ⦄ := by
  unfold runtime.store.Store.grow_table_index
  step as ⟨t, ht⟩
  have htable : t ∈ s.tables.val := by simp [ht]
  have hsize := hsizes t htable
  simp [lift]
  step as ⟨n, hn⟩
  split
  · simp [TableGrowth]
  · split
    · simp [TableGrowth]
    · step with within_spec s.table_elements (UScalar.cast .Usize delta) s.limits.max_table_elements as ⟨fits, hfits⟩
      split
      · step as ⟨t', back, ht', hback⟩
        have hsame : t' = t := by simp [ht, ht']
        obtain ⟨answer, hreserve⟩ := ha.reserve_eq t'.elements (UScalar.cast .Usize delta)
        rw [hreserve]
        cases answer
        · simp [TableGrowth]
          left
          have hrestore : back t' = s.tables := by
            rw [hback, ht']
            apply alloc.vec.Vec.ext
            simp [alloc.vec.Vec.set]
          simpa using congrArg (fun tables => {s with tables := tables}) hrestore
        · simp [TableGrowth]
          step with table_grow_loop t'.elements n (alloc.vec.Vec.len t.elements) value
            (by simp [hsame]) (by simp [hsame]; scalar_tac) (by scalar_tac) as ⟨elements, helements⟩
          step as ⟨count, hcount⟩
          right
          refine ⟨t, ?_, elements, ?_, ?_, count, ?_, ?_, ?_, rfl, ?_⟩
          · simp [ht, hindex]
          · have hn' : n.val - t'.elements.length = delta.val := by scalar_tac
            rw [hn'] at helements
            simpa [hsame] using helements
          · scalar_tac
          · scalar_tac
          · have hfit : s.table_elements.val + (UScalar.cast .Usize delta).val ≤ s.limits.max_table_elements.val := by
              simpa [hfits] using ‹fits = true›
            omega
          · scalar_tac
          · simp [hback, hsame]
      · simp [TableGrowth]

theorem cast_usize_exact (n : U64) (h : n.val ≤ Usize.max) :
    (UScalar.cast .Usize n).val = n.val := by
  apply UScalar.cast_val_mod_pow_of_inBounds_eq
  have hp : 0 < 2 ^ System.Platform.numBits := Nat.two_pow_pos _
  simp only [Usize.max, UScalarTy.numBits, Usize.numBits] at *
  omega

def MemoryGrowth {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (index : Usize) (delta : U32)
    (result : U32 × runtime.store.Store M) : Prop :=
  (result.1 = core.num.U32.MAX ∧ decodeStore view code result.2 = decodeStore view code s ∧
    (result.2 = s ∨ ∃ old : runtime.store.MemInst M, ∃ after : M,
      s.memories.val[index.val]? = some old ∧ view after = view old.buf ∧
      result.2 = {s with memories := s.memories.set index {old with buf := after}})) ∨
  ∃ old : runtime.store.MemInst M, ∃ after : M, ∃ count : Usize,
    s.memories.val[index.val]? = some old ∧
    (view after).val = (view old.buf).val ++ List.replicate (delta.val * 65536) 0#u8 ∧
    count.val = s.memory_bytes.val + delta.val * 65536 ∧
    count.val ≤ s.limits.max_memory_bytes.val ∧
    (view old.buf).length / 65536 + delta.val ≤ 65536 ∧
    (view old.buf).length / 65536 + delta.val ≤
      (core.option.Option.unwrap_or old.maximum 65536#u32).val ∧
    result.1.val = (view old.buf).length / 65536 ∧
    result.2 = {s with memories := s.memories.set index {old with buf := after}, memory_bytes := count}

theorem memory_grow_effect {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view)
    (code : CodeInterpretation) (s : runtime.store.Store M) (index : Usize) (delta : U32)
    (hindex : index.val < s.memories.length)
    (hsizes : ∀ m ∈ s.memories.val, (view m.buf).length ≤ 4294967296)
    (halign : ∀ m ∈ s.memories.val, (view m.buf).length % 65536 = 0) :
    runtime.store.Store.grow_memory_index ops s index delta ⦃ result => MemoryGrowth view code s index delta result ⦄ := by
  unfold runtime.store.Store.grow_memory_index
  step as ⟨m, hm⟩
  have hmem : m ∈ s.memories.val := by simp [hm]
  have hsize := hsizes m hmem
  rw [laws.read]
  simp [lift]
  step as ⟨old, hold⟩
  step as ⟨pages, hpages⟩
  split
  · simp [MemoryGrowth]
  · split
    · simp [MemoryGrowth]
    · step as ⟨add, hadd⟩
      split
      · simp [MemoryGrowth]
      · step as ⟨bytes, hbytes⟩
        split
        · simp [MemoryGrowth]
        · step with within_spec s.memory_bytes (UScalar.cast .Usize add) s.limits.max_memory_bytes as ⟨fits, hfits⟩
          split
          · step as ⟨m', back, hm', hback⟩
            have hcastPages : (UScalar.cast .Usize pages).val ≤ pages.val := by
              rw [UScalar.cast_val_eq]
              exact Nat.mod_le _ _
            step as ⟨newSize, hnewSize⟩
            step with laws.grow m'.buf newSize as ⟨grew, after, hafter⟩
            cases grew
            · simp only [Bool.false_eq_true, ↓reduceIte] at hafter
              simp [MemoryGrowth]
              left
              constructor
              · rw [decode_store_memory_update]
                have hdecoded : decodeMemory view {m' with buf := after} = decodeMemory view m' := by
                  simp [decodeMemory, hafter]
                simp only [hback, alloc.vec.Vec.set_val_eq, List.map_set, hdecoded]
                simp only [decodeStore, hm']
                congr 1
                have hs := List.set_getElem_self («as» := s.memories.val.map (decodeMemory view))
                  (i := index.val) (by simpa using hindex)
                simpa using hs
              · right
                refine ⟨m', ?_, after, hafter, ?_⟩
                · simp [hm', hindex]
                · simp [hback]
            · simp only [↓reduceIte] at hafter
              simp
              step as ⟨count, hcount⟩
              have haddCast : (UScalar.cast .Usize add).val = add.val :=
                cast_usize_exact add (by omega)
              have hpagesCast : (UScalar.cast .Usize pages).val = pages.val :=
                cast_usize_exact pages (by scalar_tac)
              right
              refine ⟨m, after, count, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · simp [hm, hindex]
              · have hsame : m' = m := by simp [hm, hm']
                have haligned := halign m hmem
                have hlength : newSize.val - (view m'.buf).length = delta.val * 65536 := by
                  simp only [hsame] at *
                  simp only [hpagesCast] at hnewSize
                  simp only [Slice.len_val] at hold
                  scalar_tac
                have heq := hafter.2
                rw [hlength] at heq
                simpa [hsame] using heq
              · simp only [haddCast, U32.cast_U64_val_eq] at hcount hadd
                omega
              · have hfit : s.memory_bytes.val + (UScalar.cast .Usize add).val ≤ s.limits.max_memory_bytes.val := by
                  simpa [hfits] using ‹fits = true›
                omega
              · scalar_tac
              · scalar_tac
              · scalar_tac
              · simp [hback, hm, hm']
          · simp [MemoryGrowth]

end Itasca.Runtime.Store

end

/-! ## Write -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

@[simp] theorem value_type_exact (value : runtime.Value) :
    runtime.Value.value_type value = .ok (Interp.rawType value) := by
  cases value <;> rfl

theorem check_value_owned {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (value : runtime.Value)
    (hv : Interp.ValueOwnedFits s.id value) :
    runtime.store.Store.check_value ops s value = .ok (.Ok ()) := by
  cases value <;> simp only [runtime.store.Store.check_value]
  case FuncRef address =>
    cases address with
    | none => rfl
    | some a => simp only [Interp.ValueOwnedFits] at hv; simp [runtime.store.Store.check, hv.1]
  case ExternRef address =>
    cases address with
    | none => rfl
    | some a => simp only [Interp.ValueOwnedFits] at hv; simp [runtime.store.Store.check, hv.1]

@[simp] theorem value_type_eq_self (ty : Itasca.wasm_types.ValueType) :
    wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq ty ty = .ok true := by
  cases ty <;> rfl

@[simp] theorem element_value_type_exact (ty : Itasca.wasm_types.ElemType) :
    wasm_types.ElemType.value_type ty = .ok (elementValueType ty) := by
  cases ty <;> rfl

end Itasca.Runtime.Store

end

/-! ## Define -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def objectCount {M : Type} (s : runtime.store.Store M) : Nat :=
  s.funcs.length + s.tables.length + s.memories.length + s.globals.length +
    s.externs.length + s.types.length

theorem Shape.object_count_bound {M : Type} {view : M → Slice U8}
    {s : runtime.store.Store M} (hs : Shape view s) : objectCount s ≤ s.limits.max_objects.val := by
  have h := hs.objectLimit
  unfold objectCount
  omega

@[step] theorem room_spec {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (hbound : objectCount s ≤ Usize.max) :
    runtime.store.Store.room ops s ⦃ answer => answer =
      if objectCount s < s.limits.max_objects.val then .Ok () else .Err (.Exhausted .Objects) ⦄ := by
  unfold runtime.store.Store.room
  unfold objectCount at hbound ⊢
  step
  step
  step
  step
  step
  split <;> split <;> simp_all <;> scalar_tac

theorem reserve_wrapper_eq {A T : Type} (allocator : runtime.platform.Alloc A)
    (ha : Platform.AllocCorrect allocator) (values : alloc.vec.Vec T) (extra : Usize) :
    ∃ answer : Bool, runtime.reserve allocator values extra = .ok
      ((if answer then .Ok () else .Err (.Exhausted .Allocation)), values) := by
  obtain ⟨answer, hr⟩ := ha.reserve_eq values extra
  refine ⟨answer, ?_⟩
  cases answer <;> simp [runtime.reserve, hr]

theorem ReferenceShape.mono {M : Type} (before after : runtime.store.Store M)
    (hfunc : before.funcs.length ≤ after.funcs.length)
    (hextern : before.externs.length ≤ after.externs.length)
    (ty : Itasca.wasm_types.ElemType) (word : U64) :
    ReferenceShape before ty word → ReferenceShape after ty word := by
  intro h
  rcases h with hnull | hreference
  · exact Or.inl hnull
  · right
    cases ty <;> dsimp at * <;> omega

theorem GlobalShape.mono {M : Type} (before after : runtime.store.Store M)
    (hfunc : before.funcs.length ≤ after.funcs.length)
    (hextern : before.externs.length ≤ after.externs.length)
    (global : runtime.store.GlobalInst) : GlobalShape before global → GlobalShape after global := by
  intro h
  cases ht : global.ty.valtype <;> simp only [GlobalShape, ht] at h ⊢
  all_goals try exact h
  all_goals exact ⟨ReferenceShape.mono before after hfunc hextern _ _ h.1, h.2⟩

theorem TableShape.mono {M : Type} (before after : runtime.store.Store M)
    (hfunc : before.funcs.length ≤ after.funcs.length)
    (hextern : before.externs.length ≤ after.externs.length)
    (table : runtime.store.TableInst) (h : TableShape before table) : TableShape after table := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro word hword
  exact ReferenceShape.mono before after hfunc hextern _ _ (h.2.2 word hword)

/-- Retained inst address maps remain valid when public definitions append
objects without changing store ownership. -/
theorem InstanceShape.mono {M : Type} (before after : runtime.store.Store M)
    (hid : before.id = after.id)
    (hty : before.types.length ≤ after.types.length)
    (hfn : before.funcs.length ≤ after.funcs.length)
    (htab : before.tables.length ≤ after.tables.length)
    (hmem : before.memories.length ≤ after.memories.length)
    (hglob : before.globals.length ≤ after.globals.length)
    (helem : before.elems.length ≤ after.elems.length)
    (hdata : before.datas.length ≤ after.datas.length)
    (inst : runtime.store.ModuleInst) (h : InstanceShape before inst) :
    InstanceShape after inst := by
  rcases h with ⟨htypes, hfuncs, htables, hmemories, hglobals, helems, hdatas,
    types, funcs, tables, memories, globals, elems, datas⟩
  refine ⟨htypes, hfuncs, htables, hmemories, hglobals, helems, hdatas,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro index hi; exact Nat.lt_of_lt_of_le (types index hi) hty
  · intro address ha
    exact ⟨(funcs address ha).1.trans hid, Nat.lt_of_lt_of_le (funcs address ha).2 hfn⟩
  · intro address ha
    exact ⟨(tables address ha).1.trans hid, Nat.lt_of_lt_of_le (tables address ha).2 htab⟩
  · intro address ha
    exact ⟨(memories address ha).1.trans hid, Nat.lt_of_lt_of_le (memories address ha).2 hmem⟩
  · intro address ha
    exact ⟨(globals address ha).1.trans hid, Nat.lt_of_lt_of_le (globals address ha).2 hglob⟩
  · intro index hi; exact Nat.lt_of_lt_of_le (elems index hi) helem
  · intro index hi; exact Nat.lt_of_lt_of_le (datas index hi) hdata

/-- A successful global definition appends precisely the encoded typed value. -/
theorem define_global_effect {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (s : runtime.store.Store M) (ty : Itasca.wasm_types.GlobalType) (value : runtime.Value)
    (hbound : objectCount s ≤ Usize.max) (htype : ty.valtype = Interp.rawType value)
    (hv : ValueInStore s value) :
    runtime.store.Store.define_global_with ops allocator s ty value ⦃ result =>
      (∃ error, result = (.Err error, s)) ∨
      ∃ globals : alloc.vec.Vec runtime.store.GlobalInst, ∃ words : U64 × U64,
        runtime.value.encode value = .ok words ∧
        globals.val = s.globals.val ++ [{ty, lo := words.1, hi := words.2}] ∧
        objectCount s < s.limits.max_objects.val ∧
        result = (.Ok ⟨s.id, alloc.vec.Vec.len s.globals⟩, {s with globals}) ⦄ := by
  obtain ⟨words, hencode, _⟩ := WP.spec_imp_exists (Interp.encode_value_spec value s.id hv.1)
  unfold runtime.store.Store.define_global_with
  step with room_spec ops s hbound as ⟨room, hroom⟩
  rw [hroom]
  split
  · rename_i hspace
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    rw [check_value_owned ops s value hv.1]
    simp [htype, core.result.Result.Insts.CoreOpsTry.branch,
      core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default]
    obtain ⟨answer, hr⟩ := reserve_wrapper_eq allocator ha s.globals 1#usize
    rw [hr]
    cases answer
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    · simp [core.result.Result.Insts.CoreOpsTry.branch, hencode]
      cases words with
      | mk lo hi =>
        simp
        have hmax : s.globals.length < Usize.max := by unfold objectCount at hspace; scalar_tac
        step as ⟨globals, hglobals⟩
        right
        exact ⟨globals, hglobals, hspace, rfl⟩
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca.Runtime.Store

end

/-! ## DefineMemory -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def LimitsFit (limits : Itasca.wasm_types.Limits) (maximum : U32) : Prop :=
  limits.min.val ≤ maximum.val ∧
  match limits.max with
  | none => True
  | some high => limits.min.val ≤ high.val ∧ high.val ≤ maximum.val

instance (limits : Itasca.wasm_types.Limits) (maximum : U32) : Decidable (LimitsFit limits maximum) := by
  unfold LimitsFit
  cases limits.max <;> infer_instance

@[step] theorem check_limits_spec (limits : Itasca.wasm_types.Limits) (maximum : U32) :
    runtime.store.check_limits limits maximum ⦃ result => result =
      if LimitsFit limits maximum then .Ok () else .Err .BadArguments ⦄ := by
  rcases limits with ⟨minimum, maximumOption⟩
  cases maximumOption <;> simp [runtime.store.check_limits, LimitsFit, core.option.Option.unwrap_or, lift]
  all_goals repeat' split
  all_goals simp_all
  all_goals scalar_tac

/-- Defining a memory retains exactly the supplied buffer when its view has the
requested initial size; every rejected definition leaves the store unchanged. -/
theorem define_memory_effect {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view)
    (s : runtime.store.Store M) (ty : Itasca.wasm_types.MemType) (buffer : M)
    (hbound : objectCount s ≤ Usize.max) :
    runtime.store.Store.define_memory_with ops allocator s ty buffer ⦃ result =>
      (∃ error, result = (.Err error, s)) ∨
      ∃ memories : alloc.vec.Vec (runtime.store.MemInst M), ∃ count : Usize,
        memories.val = s.memories.val ++ [{buf := buffer, maximum := ty.limits.max}] ∧
        LimitsFit ty.limits 65536#u32 ∧
        (view buffer).length = ty.limits.min.val * 65536 ∧
        objectCount s < s.limits.max_objects.val ∧
        count.val = s.memory_bytes.val + (view buffer).length ∧
        count.val ≤ s.limits.max_memory_bytes.val ∧
        result = (.Ok ⟨s.id, alloc.vec.Vec.len s.memories⟩,
          {s with memories, memory_bytes := count}) ⦄ := by
  unfold runtime.store.Store.define_memory_with
  step with room_spec ops s hbound as ⟨room, hroom⟩
  rw [hroom]
  split
  · rename_i hroom
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    step with check_limits_spec ty.limits 65536#u32 as ⟨limits, hlimits⟩
    rw [hlimits]
    by_cases hfit : LimitsFit ty.limits 65536#u32
    · simp only [if_pos hfit]
      simp [core.result.Result.Insts.CoreOpsTry.branch, lift]
      step as ⟨size, hsize⟩
      rw [laws.read]
      simp [lift]
      by_cases hlength : (view buffer).length = size.val
      · simp only [hlength, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        have hbytes : (view buffer).length = ty.limits.min.val * 65536 := by scalar_tac
        step with within_spec s.memory_bytes (Slice.len (view buffer)) s.limits.max_memory_bytes as ⟨fits, hfits⟩
        rw [hfits]
        split
        · rename_i htotal
          have htotal' : s.memory_bytes.val + (view buffer).length ≤ s.limits.max_memory_bytes.val := by simpa using htotal
          obtain ⟨answer, hr⟩ := reserve_wrapper_eq allocator ha s.memories 1#usize
          rw [hr]
          cases answer
          · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          · simp
            have hmax : s.memories.length < Usize.max := by unfold objectCount at hroom; scalar_tac
            step as ⟨memories, hmemories⟩
            have hsizeBound : size.val ≤ Usize.max := by scalar_tac
            have hcast := cast_usize_exact size hsizeBound
            step as ⟨count, hcount⟩
            right
            exact ⟨memories, hmemories, hfit, by scalar_tac, hroom, count,
              by scalar_tac, by scalar_tac, rfl⟩
        · simp
      · simp [hlength]
    · simp [hfit, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca.Runtime.Store

end

/-! ## DefineTable -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

@[step] theorem define_table_loop (count : U32) (before : alloc.vec.Vec U64) (position : U32)
    (hposition : position.val = before.length) (hbound : position.val ≤ count.val) :
    runtime.store.Store.define_table_with_loop count before position ⦃ after =>
      after.val = before.val ++ List.replicate (count.val - before.length) 0#u64 ⦄ := by
  unfold runtime.store.Store.define_table_with_loop
  apply loop.spec_decr_nat (fun pair => count.val - pair.2.val)
    (fun pair => pair.2.val = pair.1.length ∧ pair.2.val ≤ count.val ∧
      pair.1.val ++ List.replicate (count.val - pair.1.length) 0#u64 =
        before.val ++ List.replicate (count.val - before.length) 0#u64)
  · intro pair hinv
    rcases pair with ⟨items, pos⟩
    rcases hinv with ⟨hpos, hlen, hbytes⟩
    unfold runtime.store.Store.define_table_with_loop.body
    dsimp only at hpos hlen hbytes ⊢
    split
    · rename_i hmore
      have hlt : items.length < count.val := by scalar_tac
      have hpush : items.length < Usize.max := by scalar_tac
      step as ⟨after, hafter⟩
      step as ⟨next, hnext⟩
      have hlen' : after.length = items.length + 1 := by simp [hafter]
      simp only [alloc.vec.Vec.length] at *
      refine ⟨by omega, by omega, ?_, by omega⟩
      rw [hafter, List.append_assoc]
      have heq : count.val - items.val.length = (count.val - after.val.length) + 1 := by omega
      rw [heq] at hbytes
      simpa [List.replicate_succ, hlen'] using hbytes
    · rename_i hstop
      have heq : items.length = count.val := by scalar_tac
      simpa [WP.spec_ok, heq] using hbytes
  · exact ⟨hposition, hbound, rfl⟩

/-- A defined table contains exactly its requested number of null references.
All validation, resource, and allocator failures retain the original store. -/
theorem define_table_effect {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (s : runtime.store.Store M) (ty : Itasca.wasm_types.TableType)
    (hbound : objectCount s ≤ Usize.max) :
    runtime.store.Store.define_table_with ops allocator s ty ⦃ result =>
      (∃ error, result = (.Err error, s)) ∨
      ∃ tables : alloc.vec.Vec runtime.store.TableInst, ∃ elements : alloc.vec.Vec U64,
      ∃ count : Usize,
        elements.val = List.replicate ty.limits.min.val 0#u64 ∧
        tables.val = s.tables.val ++ [{elements, ty := ty.elem, maximum := ty.limits.max}] ∧
        LimitsFit ty.limits core.num.U32.MAX ∧
        objectCount s < s.limits.max_objects.val ∧
        count.val = s.table_elements.val + ty.limits.min.val ∧
        count.val ≤ s.limits.max_table_elements.val ∧
        result = (.Ok ⟨s.id, alloc.vec.Vec.len s.tables⟩,
          {s with tables, table_elements := count}) ⦄ := by
  unfold runtime.store.Store.define_table_with
  step with room_spec ops s hbound as ⟨room, hroom⟩
  rw [hroom]
  split
  · rename_i hroom
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    step with check_limits_spec ty.limits core.num.U32.MAX as ⟨limits, hlimits⟩
    rw [hlimits]
    by_cases hfit : LimitsFit ty.limits core.num.U32.MAX
    · simp [hfit, core.result.Result.Insts.CoreOpsTry.branch, lift]
      step with within_spec s.table_elements (UScalar.cast .Usize ty.limits.min)
        s.limits.max_table_elements as ⟨fits, hfits⟩
      rw [hfits]
      split
      · rename_i htotal
        have htotal' : s.table_elements.val + ty.limits.min.val ≤ s.limits.max_table_elements.val := by scalar_tac
        obtain ⟨answer, hr⟩ := reserve_wrapper_eq allocator ha (alloc.vec.Vec.new U64) (UScalar.cast .Usize ty.limits.min)
        rw [hr]
        cases answer
        · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        · simp
          step with define_table_loop ty.limits.min (alloc.vec.Vec.new U64) 0#u32 (by simp) (by scalar_tac) as ⟨elements, helements⟩
          simp [alloc.vec.Vec.new] at helements
          obtain ⟨answer, hr⟩ := reserve_wrapper_eq allocator ha s.tables 1#usize
          rw [hr]
          cases answer
          · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          · simp
            have hmax : s.tables.length < Usize.max := by unfold objectCount at hroom; scalar_tac
            step as ⟨tables, htables⟩
            step as ⟨count, hcount⟩
            right
            exact ⟨tables, elements, helements, htables, hroom, count,
              by scalar_tac, by scalar_tac, rfl⟩
      · simp
    · simp [hfit, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca.Runtime.Store

end
