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

end Exec.Store
