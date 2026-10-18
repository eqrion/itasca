import Exec.Representation.Store
import Exec.Platform.Alloc

namespace Exec.Store
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

theorem memory_grow_total {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view)
    (s : runtime.store.Store M) (index : Usize) (delta : U32)
    (hindex : index.val < s.memories.length)
    (hsizes : ∀ m ∈ s.memories.val, (view m.buf).length ≤ 4294967296) :
    runtime.store.Store.grow_memory_index ops s index delta ⦃ _ => True ⦄ := by
  unfold runtime.store.Store.grow_memory_index
  step as ⟨m, hm⟩
  have hmem : m ∈ s.memories.val := by simp [hm]
  have hsize := hsizes m hmem
  rw [laws.read]
  simp [lift]
  step as ⟨old, hold⟩
  step as ⟨pages, hpages⟩
  split
  · simp
  · split
    · simp
    · step as ⟨add, hadd⟩
      split
      · simp
      · step as ⟨bytes, hbytes⟩
        split
        · simp
        · simp [runtime.store.Store.impl.memory_bytes]
          step with within_spec s.memory_bytes (UScalar.cast .Usize add) s.limits.max_memory_bytes as ⟨fits, hfits⟩
          split
          · step as ⟨m', back, hm', hback⟩
            have hcastPages : (UScalar.cast .Usize pages).val ≤ pages.val := by
              rw [UScalar.cast_val_eq]
              exact Nat.mod_le _ _
            step as ⟨newSize, hnewSize⟩
            step with laws.grow m'.buf newSize as ⟨grew, after, hafter⟩
            cases grew
            · simp
            · simp
              step
          · simp

def TableGrowth {M : Type} (s : runtime.store.Store M) (index : Usize)
    (delta : U32) (value : U64) (result : U32 × runtime.store.Store M) : Prop :=
  (result.1 = core.num.U32.MAX ∧ result.2 = s) ∨
  ∃ old : runtime.store.Table, ∃ elements : alloc.vec.Vec U64, ∃ count : Usize,
    s.tables.val[index.val]? = some old ∧
    elements.val = old.elements.val ++ List.replicate delta.val value ∧
    old.elements.length + delta.val ≤ U32.max ∧
    count.val = s.table_elements.val + delta.val ∧
    count.val ≤ s.limits.max_table_elements.val ∧
    old.elements.length + delta.val ≤ (core.option.Option.unwrap_or old.maximum core.num.U32.MAX).val ∧
    result = (UScalar.cast .U32 (alloc.vec.Vec.len old.elements),
      {s with tables := s.tables.set index {old with elements := elements}, table_elements := count})

theorem table_grow_total {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (s : runtime.store.Store M) (index : Usize) (delta : U32) (value : U64)
    (hindex : index.val < s.tables.length)
    (hsizes : ∀ t ∈ s.tables.val, t.elements.length ≤ U32.max) :
    runtime.store.Store.grow_table_index ops allocator s index delta value ⦃ _ => True ⦄ := by
  unfold runtime.store.Store.grow_table_index
  step as ⟨t, ht⟩
  have htable : t ∈ s.tables.val := by simp [ht]
  have hsize := hsizes t htable
  simp [lift]
  step as ⟨n, hn⟩
  split
  · simp
  · split
    · simp
    · simp [runtime.store.Store.impl.table_elements]
      step with within_spec s.table_elements (UScalar.cast .Usize delta) s.limits.max_table_elements as ⟨fits, hfits⟩
      split
      · step as ⟨t', back, ht', hback⟩
        have hsame : t' = t := by simp [ht, ht']
        obtain ⟨answer, hreserve⟩ := ha.reserve_eq t'.elements (UScalar.cast .Usize delta)
        rw [hreserve]
        cases answer
        · simp
        · simp
          step with table_grow_loop t'.elements n (alloc.vec.Vec.len t.elements) value
            (by simp [hsame]) (by simp [hsame]; scalar_tac) (by scalar_tac)
          step
      · simp

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
    · simp [runtime.store.Store.impl.table_elements]
      step with within_spec s.table_elements (UScalar.cast .Usize delta) s.limits.max_table_elements as ⟨fits, hfits⟩
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
    (result.2 = s ∨ ∃ old : runtime.store.Memory M, ∃ after : M,
      s.memories.val[index.val]? = some old ∧ view after = view old.buf ∧
      result.2 = {s with memories := s.memories.set index {old with buf := after}})) ∨
  ∃ old : runtime.store.Memory M, ∃ after : M, ∃ count : Usize,
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
        · simp [runtime.store.Store.impl.memory_bytes]
          step with within_spec s.memory_bytes (UScalar.cast .Usize add) s.limits.max_memory_bytes as ⟨fits, hfits⟩
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
              · rw [decodeStore_memory_update]
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



/-- Memory's failure sentinel cannot be a successful old size because WebAssembly
memories have at most 65536 pages. Failure preserves the entire decoded store. -/
theorem memory_grow_failure_unchanged {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view)
    (code : CodeInterpretation) (s : runtime.store.Store M) (index : Usize) (delta : U32)
    (hindex : index.val < s.memories.length)
    (hsizes : ∀ m ∈ s.memories.val, (view m.buf).length ≤ 4294967296)
    (halign : ∀ m ∈ s.memories.val, (view m.buf).length % 65536 = 0) :
    runtime.store.Store.grow_memory_index ops s index delta ⦃ result =>
      result.1 = core.num.U32.MAX → decodeStore view code result.2 = decodeStore view code s ⦄ := by
  apply WP.spec_mono (memory_grow_effect ops view laws code s index delta hindex hsizes halign)
  intro result effect hfailed
  rcases effect with hfailure | ⟨old, after, count, hlookup, _, _, _, _, _, hreturn, _⟩
  · exact hfailure.2.1
  · have hbound := hsizes old (List.mem_of_getElem? hlookup)
    rw [hfailed] at hreturn
    change 4294967295 = (view old.buf).length / 65536 at hreturn
    omega

/-- A table's all-ones return value is also the valid old size of a maximal
zero-growth success; this statement keeps that successful case explicit. -/
theorem table_grow_failure_or_maximal_zero {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (s : runtime.store.Store M) (index : Usize) (delta : U32) (value : U64)
    (hindex : index.val < s.tables.length)
    (hsizes : ∀ t ∈ s.tables.val, t.elements.length ≤ U32.max) :
    runtime.store.Store.grow_table_index ops allocator s index delta value ⦃ result =>
      result.1 = core.num.U32.MAX → result.2 = s ∨
        ∃ old : runtime.store.Table, s.tables.val[index.val]? = some old ∧
          old.elements.length = U32.max ∧ delta.val = 0 ⦄ := by
  apply WP.spec_mono (table_grow_effect ops allocator ha s index delta value hindex hsizes)
  intro result effect hfailed
  rcases effect with hfailure | ⟨old, elements, count, hlookup, _, hnewbound, _, _, _, heq⟩
  · exact Or.inl hfailure.2
  · right
    refine ⟨old, hlookup, ?_⟩
    have hbound := hsizes old (List.mem_of_getElem? hlookup)
    have hr := congrArg Prod.fst heq
    rw [hfailed] at hr
    have hrval := congrArg (fun x : U32 => x.val) hr
    change 4294967295 = (UScalar.cast .U32 (alloc.vec.Vec.len old.elements)).val at hrval
    scalar_tac


/-- Even the maximal zero-growth success leaves the store unchanged, so the
numeric table sentinel has a uniform unchanged-store guarantee. -/
theorem table_grow_sentinel_unchanged {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (s : runtime.store.Store M) (index : Usize) (delta : U32) (value : U64)
    (hindex : index.val < s.tables.length)
    (hsizes : ∀ t ∈ s.tables.val, t.elements.length ≤ U32.max) :
    runtime.store.Store.grow_table_index ops allocator s index delta value ⦃ result =>
      result.1 = core.num.U32.MAX → result.2 = s ⦄ := by
  apply WP.spec_mono (table_grow_effect ops allocator ha s index delta value hindex hsizes)
  intro result effect hfailed
  rcases effect with hfailure | ⟨old, elements, count, hlookup, helements, hnewbound, hcount, _, _, heq⟩
  · exact hfailure.2
  · have hbound := hsizes old (List.mem_of_getElem? hlookup)
    have hr := congrArg (fun pair => pair.1.val) heq
    rw [hfailed] at hr
    change 4294967295 = (UScalar.cast .U32 (alloc.vec.Vec.len old.elements)).val at hr
    have hzero : delta.val = 0 := by scalar_tac
    have helems : elements = old.elements := by
      apply alloc.vec.Vec.ext
      simpa [hzero] using helements
    have hcount' : count = s.table_elements := by
      apply UScalar.eq_of_val_eq
      simpa only [hzero, Nat.add_zero] using hcount
    have hold : old = s.tables.val[index.val] := by
      simp only [List.getElem?_eq_getElem hindex, Option.some.injEq] at hlookup
      exact hlookup.symm
    have hrestore : s.tables.set index old = s.tables := by
      rw [hold]
      apply alloc.vec.Vec.ext
      simp [alloc.vec.Vec.set]
    rw [heq]
    simp [helems, hcount', hrestore]

end Exec.Store
