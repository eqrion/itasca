import Exec.Store.Invariant.Rejected

namespace Exec.Store
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

/-- External identity allocation either leaves the store unchanged or appends
exactly the requested identity and returns its stable store-owned index. -/
theorem define_extern_effect {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (s : runtime.store.Store M) (identity : U64) (hbound : objectCount s ≤ Usize.max) :
    runtime.store.Store.define_extern_with ops allocator s identity ⦃ result =>
      (∃ error, result = (.Err error, s)) ∨
      ∃ externs : alloc.vec.Vec U64, externs.val = s.externs.val ++ [identity] ∧
        objectCount s < s.limits.max_objects.val ∧
        result = (.Ok ⟨s.id, alloc.vec.Vec.len s.externs⟩, {s with externs}) ⦄ := by
  unfold runtime.store.Store.define_extern_with
  step with room_spec ops s hbound as ⟨room, hroom⟩
  rw [hroom]
  split
  · rename_i hspace
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    obtain ⟨answer, hr⟩ := reserve_wrapper_eq allocator ha s.externs 1#usize
    rw [hr]
    cases answer
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    · simp [core.result.Result.Insts.CoreOpsTry.branch]
      have hmax : s.externs.length < Usize.max := by unfold objectCount at hspace; scalar_tac
      step as ⟨externs, hext⟩
      right
      exact ⟨externs, hext, hspace, rfl⟩
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]


theorem ReferenceShape.mono {M : Type} (before after : runtime.store.Store M)
    (hfunc : before.funcs.length ≤ after.funcs.length)
    (hextern : before.externs.length ≤ after.externs.length)
    (ty : Itasca.types.ElemType) (word : U64) :
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

/-- Appending an external identity preserves every existing reference and all
retained-object accounting; the returned handle is immediately usable. -/
theorem define_extern_preserves_shape {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (s : runtime.store.Store M) (hs : Shape view s) (identity : U64) :
    runtime.store.Store.define_extern_with ops allocator s identity ⦃ result => Shape view result.2 ⦄ := by
  have hbound : objectCount s ≤ Usize.max := by
    have h := hs.object_count_bound
    scalar_tac
  apply WP.spec_mono (define_extern_effect ops allocator ha s identity hbound)
  intro result effect
  rcases effect with ⟨error, unchanged⟩ | ⟨externs, hext, hroom, hresult⟩
  · simpa [unchanged] using hs
  · rw [hresult]
    have hlen : s.externs.length ≤ externs.length := by simp [hext]
    constructor
    · exact hs.identity
    · simpa [FunctionShape] using hs.functions
    · exact hs.memories
    · intro table htable
      exact TableShape.mono s _ (by simp) hlen table (hs.tables table htable)
    · intro global hglobal
      exact GlobalShape.mono s _ (by simp) hlen global (hs.globals global hglobal)
    · intro element helement word hword
      exact ReferenceShape.mono s _ (by simp) hlen _ _ (hs.elements element helement word hword)
    · simpa [InstanceShape] using hs.instances
    · exact hs.canonicalTypes
    · simp only [alloc.vec.Vec.length, hext, List.length_append, List.length_singleton]
      unfold objectCount at hroom
      simp only [alloc.vec.Vec.length] at hroom
      omega
    · exact hs.instanceLimit
    · exact hs.instanceAccounting
    · exact hs.instanceItemLimit
    · exact hs.signatureAccounting
    · exact hs.signatureLimit
    · exact hs.memoryAccounting
    · exact hs.memoryLimit
    · exact hs.tableAccounting
    · exact hs.tableLimit


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
    (s : runtime.store.Store M) (ty : Itasca.types.GlobalType) (value : runtime.Value)
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

/-- New globals preserve every retained object and inst address map. -/
theorem define_global_preserves_shape {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (s : runtime.store.Store M) (hs : Shape view s)
    (ty : Itasca.types.GlobalType) (value : runtime.Value)
    (htype : ty.valtype = Interp.rawType value) (hv : ValueInStore s value) :
    runtime.store.Store.define_global_with ops allocator s ty value ⦃ result => Shape view result.2 ⦄ := by
  have hbound : objectCount s ≤ Usize.max := by
    have h := hs.object_count_bound
    scalar_tac
  apply WP.spec_mono (define_global_effect ops allocator ha s ty value hbound htype hv)
  intro result effect
  rcases effect with ⟨error, unchanged⟩ | ⟨globals, words, hencode, hglobals, hroom, hresult⟩
  · simpa [unchanged] using hs
  · have hcanonical := encode_global_shape s value ty htype hv
    rw [hencode] at hcanonical
    simp only [WP.spec_ok] at hcanonical
    rw [hresult]
    have hlen : s.globals.length ≤ globals.length := by simp [hglobals]
    constructor
    · exact hs.identity
    · simpa [FunctionShape] using hs.functions
    · exact hs.memories
    · simpa [TableShape, ReferenceShape] using hs.tables
    · intro global hmember
      rw [hglobals] at hmember
      rcases List.mem_append.mp hmember with old | fresh
      · simpa [GlobalShape, ReferenceShape] using hs.globals global old
      · simp only [List.mem_singleton] at fresh
        subst global
        simpa [GlobalShape, ReferenceShape] using hcanonical
    · simpa [ReferenceShape] using hs.elements
    · intro inst hinstance
      exact InstanceShape.mono s {s with globals} rfl (by simp) (by simp) (by simp) (by simp)
        hlen (by simp) (by simp) inst (hs.instances inst hinstance)
    · exact hs.canonicalTypes
    · simp only [alloc.vec.Vec.length, hglobals, List.length_append, List.length_singleton]
      unfold objectCount at hroom
      simp only [alloc.vec.Vec.length] at hroom
      omega
    · exact hs.instanceLimit
    · exact hs.instanceAccounting
    · exact hs.instanceItemLimit
    · exact hs.signatureAccounting
    · exact hs.signatureLimit
    · exact hs.memoryAccounting
    · exact hs.memoryLimit
    · exact hs.tableAccounting
    · exact hs.tableLimit

end Exec.Store
