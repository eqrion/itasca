import Exec.Store.Invariant.TypeEquality

namespace Exec.Store
open Aeneas Aeneas.Std

def scanState {M : Type} (s : runtime.store.Store M) (i : Usize) :=
  (s.id, s.limits, s.funcs, s.types, s.tables, s.memories, s.globals, s.instances,
    s.elems, s.datas, s.externs, s.instance_items, s.signature_values,
    s.memory_bytes, s.table_elements, i)

/-- Signature search returns the first matching retained signature, or its
exact end index, without changing any store field. -/
theorem intern_scan {M : Type} (s : runtime.store.Store M) (ty : Itasca.types.FuncType)
    (position : Usize) (hpos : position.val ≤ s.types.length)
    (hprefix : ty ∉ s.types.val.take position.val) :
    runtime.store.Store.intern_type_loop s ty position ⦃ result =>
      ∃ index : Usize, result = scanState s index ∧ index.val ≤ s.types.length ∧
        ty ∉ s.types.val.take index.val ∧
        (s.types.val[index.val]? = some ty ∨ index.val = s.types.length) ⦄ := by
  unfold runtime.store.Store.intern_type_loop
  apply loop.spec_decr_nat (fun index => s.types.length - index.val)
    (fun index => index.val ≤ s.types.length ∧ ty ∉ s.types.val.take index.val)
  · intro index ⟨hindex, hprefix⟩
    unfold runtime.store.Store.intern_type_loop.body
    dsimp only
    split
    · rename_i hmore
      have hi : index.val < s.types.length := by scalar_tac
      step as ⟨existing, hexisting⟩
      step with same_func_type_spec existing ty as ⟨same, hsame⟩
      cases same
      · simp
        have hne : s.types.val[index.val] ≠ ty := by simpa [hexisting] using hsame
        step as ⟨next, hnext⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hnext, List.take_succ_eq_append_getElem hi]
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨hprefix, ne_comm.mp hne⟩
      · simp
        refine ⟨index, rfl, hindex, hprefix, Or.inl ?_⟩
        have heq : s.types.val[index.val] = ty := by simpa [hexisting] using hsame
        simp [List.getElem?_eq_getElem hi, heq]
    · rename_i hstop
      have heq : index.val = s.types.length := by scalar_tac
      simp only [WP.spec_ok]
      exact ⟨index, rfl, hindex, hprefix, Or.inr heq⟩
  · exact ⟨hpos, hprefix⟩

def InternEffect {M : Type} (s : runtime.store.Store M) (ty : Itasca.types.FuncType)
    (result : core.result.Result Usize runtime.ExecError × runtime.store.Store M) : Prop :=
  (∃ error, result = (.Err error, s)) ∨
  (∃ index, s.types.val[index.val]? = some ty ∧ result = (.Ok index, s)) ∨
  (∃ types : alloc.vec.Vec Itasca.types.FuncType, ∃ count : Usize,
    types.val = s.types.val ++ [ty] ∧ ty ∉ s.types.val ∧
    objectCount s < s.limits.max_objects.val ∧
    count.val = s.signature_values.val + ty.params.length + ty.results.length ∧
    count.val ≤ s.limits.max_signature_values.val ∧
    result = (.Ok (alloc.vec.Vec.len s.types), {s with types, signature_values := count}))

/-- Signature interning preserves existing canonical indices and appends at
most one exact copy of a previously absent signature. -/
theorem intern_type_effect {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (s : runtime.store.Store M) (ty : Itasca.types.FuncType)
    (hbound : objectCount s ≤ Usize.max) :
    runtime.store.Store.intern_type ops allocator s ty ⦃ result => InternEffect s ty result ⦄ := by
  obtain ⟨scanned, hscan, index, hstate, hi, hprefix, hfound⟩ :=
    WP.spec_imp_exists (intern_scan s ty 0#usize (by scalar_tac) (by simp))
  rw [hstate] at hscan
  unfold runtime.store.Store.intern_type
  rw [hscan]
  simp [scanState]
  split
  · rename_i hless
    simp only [WP.spec_ok]
    right; left
    refine ⟨index, ?_, rfl⟩
    rcases hfound with found | hend
    · exact found
    · scalar_tac
  · rename_i hnotless
    have hend : index.val = s.types.length := by scalar_tac
    have hindex : index = alloc.vec.Vec.len s.types := by scalar_tac
    have habsent : ty ∉ s.types.val := by simpa [hend] using hprefix
    step as ⟨size, hsize⟩
    cases size with
    | none =>
      simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, InternEffect]
    | some size =>
      simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch]
      step with within_spec s.signature_values size s.limits.max_signature_values as ⟨fits, hfits⟩
      rw [hfits]
      split
      · rename_i hbudget
        step with room_spec ops s hbound as ⟨room, hroom⟩
        rw [hroom]
        by_cases hspace : objectCount s < s.limits.max_objects.val
        · simp only [if_pos hspace]
          simp [core.result.Result.Insts.CoreOpsTry.branch]
          obtain ⟨answer, hr⟩ := reserve_wrapper_eq allocator ha s.types 1#usize
          rw [hr]
          cases answer
          · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, InternEffect]
          · simp
            step with copy_type_spec allocator ha ty as ⟨copied, hcopied⟩
            rcases hcopied with hok | herr
            · rw [hok]
              simp [core.result.Result.Insts.CoreOpsTry.branch]
              have hmax : s.types.length < Usize.max := by unfold objectCount at hspace; scalar_tac
              step as ⟨types, htypes⟩
              step as ⟨count, hcount⟩
              right; right
              exact ⟨types, count, htypes, habsent, hspace, by scalar_tac, by scalar_tac, by simp [hindex]⟩
            · simp [herr, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, InternEffect]
        · simp [hspace, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, InternEffect]
      · simp [InternEffect]

theorem FunctionShape.more_types {M : Type} (before after : runtime.store.Store M)
    (htypes : before.types.length ≤ after.types.length)
    (hinstances : before.instances = after.instances)
    (function : runtime.store.Function) (h : FunctionShape before function) :
    FunctionShape after function := by
  refine ⟨Nat.lt_of_lt_of_le h.1 htypes, ?_⟩
  have hcode := h.2
  cases hc : function.code <;> simpa [hc, hinstances] using hcode

/-- Extending the canonical type pool preserves every retained object's type
index, and extends only the signature-value accounting total. -/
theorem Shape.append_type {M : Type} (view : M → Slice U8)
    (s : runtime.store.Store M) (hs : Shape view s) (ty : Itasca.types.FuncType)
    (types : alloc.vec.Vec Itasca.types.FuncType) (count : Usize)
    (htypes : types.val = s.types.val ++ [ty]) (habsent : ty ∉ s.types.val)
    (hroom : objectCount s < s.limits.max_objects.val)
    (hcount : count.val = s.signature_values.val + ty.params.length + ty.results.length)
    (hlimit : count.val ≤ s.limits.max_signature_values.val) :
    Shape view {s with types, signature_values := count} := by
  have hlen : s.types.length ≤ types.length := by simp [htypes]
  constructor
  · exact hs.identity
  · intro function hfunction
    exact FunctionShape.more_types s {s with types, signature_values := count}
      hlen rfl function (hs.functions function hfunction)
  · exact hs.memories
  · simpa [TableShape, ReferenceShape] using hs.tables
  · simpa [GlobalShape, ReferenceShape] using hs.globals
  · simpa [ReferenceShape] using hs.elements
  · intro inst hinst
    exact InstanceShape.mono s {s with types, signature_values := count} rfl
      hlen (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      inst (hs.instances inst hinst)
  · have hnot : decodeFuncType ty ∉ s.types.val.map decodeFuncType := by
      intro hmember
      obtain ⟨existing, hexisting, heq⟩ := List.mem_map.mp hmember
      have same := decodeFuncType_injective heq
      subst existing
      exact habsent hexisting
    simp [htypes, List.nodup_append, hs.canonicalTypes]
    intro existing hexisting heq
    have same := decodeFuncType_injective heq
    subst existing
    exact habsent hexisting
  · simp only [alloc.vec.Vec.length, htypes, List.length_append, List.length_singleton]
    unfold objectCount at hroom
    simp only [alloc.vec.Vec.length] at hroom
    omega
  · exact hs.instanceLimit
  · exact hs.instanceAccounting
  · exact hs.instanceItemLimit
  · simp [htypes, hcount, hs.signatureAccounting, Nat.add_assoc]
  · exact hlimit
  · exact hs.memoryAccounting
  · exact hs.memoryLimit
  · exact hs.tableAccounting
  · exact hs.tableLimit

/-- Interning preserves the full structural store invariant and makes every
successful returned index resolve to exactly the requested signature. -/
theorem intern_type_preserves_shape {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (s : runtime.store.Store M) (hs : Shape view s)
    (ty : Itasca.types.FuncType) :
    runtime.store.Store.intern_type ops allocator s ty ⦃ result =>
      Shape view result.2 ∧ ∀ index, result.1 = .Ok index → result.2.types.val[index.val]? = some ty ⦄ := by
  have hbound : objectCount s ≤ Usize.max := by
    have h := hs.object_count_bound
    scalar_tac
  apply WP.spec_mono (intern_type_effect ops allocator ha s ty hbound)
  intro result effect
  rcases effect with ⟨error, unchanged⟩ | ⟨index, hlookup, unchanged⟩ |
    ⟨types, count, htypes, habsent, hroom, hcount, hlimit, hresult⟩
  · simp [unchanged, hs]
  · simp [unchanged, hs, hlookup]
  · rw [hresult]
    refine ⟨Shape.append_type view s hs ty types count htypes habsent hroom hcount hlimit, ?_⟩
    intro index hindex
    simp only [core.result.Result.Ok.injEq] at hindex
    subst index
    simp [htypes]

end Exec.Store

