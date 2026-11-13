import Itasca.Generated.FunsInstantiate
import Itasca.Runtime.Store.Api.DefineTable
import Itasca.Runtime.Representation.StoreCapacity

/-!
Sections, each formerly its own module: CopyTypes, TypeEquality, InternTypes, Rollback.
-/

/-! ## CopyTypes -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

@[step] theorem copy_type_loop (source target : alloc.vec.Vec Itasca.wasm_types.ValueType)
    (position : Usize) (hpos : position.val ≤ source.length)
    (htarget : target.val = source.val.take position.val) :
    runtime.copy_type_loop0 source target position ⦃ after => after = source ⦄ := by
  unfold runtime.copy_type_loop0
  apply loop.spec_decr_nat (fun pair => source.length - pair.2.val)
    (fun pair => pair.2.val ≤ source.length ∧ pair.1.val = source.val.take pair.2.val)
  · intro pair hinv
    rcases pair with ⟨items, pos⟩
    rcases hinv with ⟨hpos, hitems⟩
    unfold runtime.copy_type_loop0.body
    dsimp only at hpos hitems ⊢
    split
    · rename_i hmore
      have hi : pos.val < source.length := by scalar_tac
      have hlen : items.length = pos.val := by simp [hitems, Nat.min_eq_left hpos]
      have hmax : items.length < Usize.max := by scalar_tac
      step as ⟨value, hvalue⟩
      step as ⟨after, hafter⟩
      step as ⟨next, hnext⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hafter, hitems, hnext, List.take_succ_eq_append_getElem hi, hvalue]
    · rename_i hstop
      have heq : pos.val = source.length := by scalar_tac
      simp only [WP.spec_ok]
      apply alloc.vec.Vec.ext
      simpa [heq] using hitems
  · exact ⟨hpos, htarget⟩

@[step] theorem copy_type_loop_results (source target : alloc.vec.Vec Itasca.wasm_types.ValueType)
    (position : Usize) (hpos : position.val ≤ source.length)
    (htarget : target.val = source.val.take position.val) :
    runtime.copy_type_loop1 source target position ⦃ after => after = source ⦄ := by
  have heq : runtime.copy_type_loop1 source target position = runtime.copy_type_loop0 source target position := by rfl
  rw [heq]
  exact copy_type_loop source target position hpos htarget

/-- Type copying preserves the entire signature, or reports only an allocation
failure; allocator capacity changes cannot change any value. -/
theorem copy_type_spec {A : Type} (allocator : runtime.platform.Alloc A)
    (ha : Platform.AllocCorrect allocator) (ty : Itasca.wasm_types.FuncType) :
    runtime.copy_type allocator ty ⦃ answer =>
      answer = .Ok ty ∨ answer = .Err (.Exhausted .Allocation) ⦄ := by
  unfold runtime.copy_type
  dsimp only
  obtain ⟨answer, hr⟩ := reserve_wrapper_eq allocator ha (alloc.vec.Vec.new Itasca.wasm_types.ValueType) (alloc.vec.Vec.len ty.params)
  rw [hr]
  cases answer
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp [core.result.Result.Insts.CoreOpsTry.branch]
    obtain ⟨answer, hr⟩ := reserve_wrapper_eq allocator ha (alloc.vec.Vec.new Itasca.wasm_types.ValueType) (alloc.vec.Vec.len ty.results)
    rw [hr]
    cases answer
    · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    · simp
      step with copy_type_loop ty.params (alloc.vec.Vec.new Itasca.wasm_types.ValueType) 0#usize (by scalar_tac) (by simp) as ⟨params, hp⟩
      step with copy_type_loop_results ty.results (alloc.vec.Vec.new Itasca.wasm_types.ValueType) 0#usize (by scalar_tac) (by simp) as ⟨results, hr⟩
      simp [hp, hr]

end Itasca.Runtime.Store

end

/-! ## TypeEquality -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

@[step] theorem value_type_equal (a b : Itasca.wasm_types.ValueType) :
    wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq a b ⦃ equal => equal = true ↔ a = b ⦄ := by
  cases a <;> cases b <;> simp [
    Itasca.wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq]

@[step] theorem same_func_type_loop (left right : alloc.vec.Vec Itasca.wasm_types.ValueType)
    (position : Usize) (same : Bool) (gate : Prop) (hlen : left.length = right.length)
    (hpos : position.val ≤ left.length)
    (hprefix : same = true ↔ gate ∧ left.val.take position.val = right.val.take position.val) :
    runtime.store.same_func_type_loop0 left right position same ⦃ answer => answer = true ↔ gate ∧ left = right ⦄ := by
  unfold runtime.store.same_func_type_loop0
  apply loop.spec_decr_nat (fun pair => left.length - pair.1.val)
    (fun pair => pair.1.val ≤ left.length ∧
      (pair.2 = true ↔ gate ∧ left.val.take pair.1.val = right.val.take pair.1.val))
  · intro pair hinv
    rcases pair with ⟨pos, same⟩
    rcases hinv with ⟨hpos, hprefix⟩
    unfold runtime.store.same_func_type_loop0.body
    dsimp only at hpos hprefix ⊢
    split
    · rename_i hmore
      have hi : pos.val < left.length := by scalar_tac
      have hi' : pos.val < right.length := by omega
      cases same
      · simp
        intro hgate heq
        subst right
        simp [hgate] at hprefix
      · simp
        have hp : left.val.take pos.val = right.val.take pos.val := (hprefix.mp rfl).2
        have hg := (hprefix.mp rfl).1
        step as ⟨a, ha⟩
        step as ⟨b, hb⟩
        step with value_type_equal a b as ⟨equal, hequal⟩
        step as ⟨next, hnext⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hnext, List.take_succ_eq_append_getElem hi, List.take_succ_eq_append_getElem hi', hp]
        simpa only [hg, true_and, ha, hb, List.append_cancel_left_eq, List.singleton_inj] using hequal
    · rename_i hstop
      have hend : pos.val = left.length := by scalar_tac
      simp only [WP.spec_ok]
      rw [hend] at hprefix
      simp only [alloc.vec.Vec.length, List.take_length] at hprefix
      have hr : right.val.take left.val.length = right.val := by simpa [hlen] using List.take_length right.val
      rw [hr] at hprefix
      constructor
      · intro ht
        exact ⟨(hprefix.mp ht).1, alloc.vec.Vec.ext _ _ (hprefix.mp ht).2⟩
      · intro heq
        exact hprefix.mpr ⟨heq.1, congrArg alloc.vec.Vec.val heq.2⟩
  · exact ⟨hpos, hprefix⟩

@[step] theorem same_func_results_loop (left right : alloc.vec.Vec Itasca.wasm_types.ValueType)
    (position : Usize) (same : Bool) (gate : Prop) (hlen : left.length = right.length)
    (hpos : position.val ≤ left.length)
    (hprefix : same = true ↔ gate ∧ left.val.take position.val = right.val.take position.val) :
    runtime.store.same_func_type_loop1 left right position same ⦃ answer => answer = true ↔ gate ∧ left = right ⦄ := by
  have heq : runtime.store.same_func_type_loop1 left right position same =
      runtime.store.same_func_type_loop0 left right position same := by rfl
  rw [heq]
  exact same_func_type_loop left right position same gate hlen hpos hprefix

/-- The actual canonical-signature comparison is total and recognizes exact
parameter and result equality. -/
@[step] theorem same_func_type_spec (left right : Itasca.wasm_types.FuncType) :
    runtime.store.same_func_type left right ⦃ answer => answer = true ↔ left = right ⦄ := by
  unfold runtime.store.same_func_type
  dsimp only
  split
  · rename_i hne
    simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    intro heq
    subst right
    simp at hne
  · rename_i hparams
    split
    · rename_i hne
      simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
      intro heq
      subst right
      simp at hne
    · rename_i hresults
      have hp : left.params.length = right.params.length := by scalar_tac
      have hr : left.results.length = right.results.length := by scalar_tac
      step with same_func_type_loop left.params right.params 0#usize true True hp
        (by scalar_tac) (by simp) as ⟨same, hsame⟩
      step with same_func_results_loop left.results right.results 0#usize same
        (left.params = right.params) hr (by scalar_tac) (by simpa using hsame) as ⟨answer, hanswer⟩
      rw [hanswer]
      cases left
      cases right
      simp

theorem source_type_injective : Function.Injective Interp.sourceType := by
  intro a b heq
  cases a <;> cases b <;> simp_all [Interp.sourceType]

theorem decode_func_type_injective : Function.Injective decodeFuncType := by
  intro a b heq
  cases a with
  | mk ap ar =>
    cases b with
    | mk bp br =>
      simp only [decodeFuncType, functype.mk_functype.injEq, list.mk_list.injEq] at heq
      have hp := List.map_injective_iff.mpr source_type_injective heq.1
      have hr := List.map_injective_iff.mpr source_type_injective heq.2
      have hp' := alloc.vec.Vec.ext ap bp hp
      have hr' := alloc.vec.Vec.ext ar br hr
      cases hp'
      cases hr'
      rfl

end Itasca.Runtime.Store

end

/-! ## InternTypes -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def scanState {M : Type} (s : runtime.store.Store M) (i : Usize) :=
  (s.id, s.limits, s.funcs, s.types, s.tables, s.memories, s.globals, s.instances,
    s.elems, s.datas, s.externs, s.instance_items, s.signature_values,
    s.memory_bytes, s.table_elements, i)

/-- Signature search returns the first matching retained signature, or its
exact end index, without changing any store field. -/
theorem intern_scan {M : Type} (s : runtime.store.Store M) (ty : Itasca.wasm_types.FuncType)
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

def InternEffect {M : Type} (s : runtime.store.Store M) (ty : Itasca.wasm_types.FuncType)
    (result : core.result.Result Usize runtime.ExecError × runtime.store.Store M) : Prop :=
  (∃ error, result = (.Err error, s)) ∨
  (∃ index, s.types.val[index.val]? = some ty ∧ result = (.Ok index, s)) ∨
  (∃ types : alloc.vec.Vec Itasca.wasm_types.FuncType, ∃ count : Usize,
    types.val = s.types.val ++ [ty] ∧ ty ∉ s.types.val ∧
    objectCount s < s.limits.max_objects.val ∧
    count.val = s.signature_values.val + ty.params.length + ty.results.length ∧
    count.val ≤ s.limits.max_signature_values.val ∧
    result = (.Ok (alloc.vec.Vec.len s.types), {s with types, signature_values := count}))

/-- Signature interning preserves existing canonical indices and appends at
most one exact copy of a previously absent signature. -/
theorem intern_type_effect {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (s : runtime.store.Store M) (ty : Itasca.wasm_types.FuncType)
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

end Itasca.Runtime.Store

end

/-! ## Rollback -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

private def trimBody {T : Type} (n : Usize) (v : alloc.vec.Vec T) :
    Result (ControlFlow (alloc.vec.Vec T) (alloc.vec.Vec T)) := do
  let i := alloc.vec.Vec.len v
  if i > n then
    let (_, rest) ← alloc.vec.Vec.pop Global v
    .ok (.cont rest)
  else .ok (.done v)

/-- Removing provisional suffixes terminates and retains exactly the original
prefix, including every value in that prefix. -/
private theorem trim_spec {T : Type} (n : Usize) (v : alloc.vec.Vec T) :
    loop (trimBody n) v ⦃ after => after.val = v.val.take n.val ⦄ := by
  apply loop.spec_decr_nat (fun items => items.length)
    (fun items => items.val.take n.val = v.val.take n.val)
  · intro items hinv
    unfold trimBody
    dsimp only
    split
    · rename_i hmore
      have hlt : n.val < items.val.length := by scalar_tac
      simp [alloc.vec.Vec.pop, alloc.vec.Vec.length]
      refine ⟨?_, ?_⟩
      · simpa only [List.dropLast_eq_take, List.take_take, Nat.min_eq_left (by omega : n.val ≤ items.val.length - 1)] using hinv
      · omega
    · rename_i hstop
      have hle : items.length ≤ n.val := by scalar_tac
      simpa only [WP.spec_ok, List.take_of_length_le hle] using hinv
  · rfl

@[step] theorem rollback_loop1 (items : alloc.vec.Vec (runtime.store.DataInst)) (n : Usize) :
    runtime.store.instantiate.Store.instantiate_with_loop1 items n ⦃ after =>
      after.val = items.val.take n.val ⦄ := by
  change loop (trimBody n) items ⦃ after => after.val = items.val.take n.val ⦄
  exact trim_spec n items

@[step] theorem rollback_loop2 (items : alloc.vec.Vec (runtime.store.ModuleInst)) (n : Usize) :
    runtime.store.instantiate.Store.instantiate_with_loop2 items n ⦃ after =>
      after.val = items.val.take n.val ⦄ := by
  change loop (trimBody n) items ⦃ after => after.val = items.val.take n.val ⦄
  exact trim_spec n items

@[step] theorem rollback_loop3 (items : alloc.vec.Vec (runtime.store.FuncInst)) (n : Usize) :
    runtime.store.instantiate.Store.instantiate_with_loop3 items n ⦃ after =>
      after.val = items.val.take n.val ⦄ := by
  change loop (trimBody n) items ⦃ after => after.val = items.val.take n.val ⦄
  exact trim_spec n items

@[step] theorem rollback_loop4 (items : alloc.vec.Vec (runtime.store.TableInst)) (n : Usize) :
    runtime.store.instantiate.Store.instantiate_with_loop4 items n ⦃ after =>
      after.val = items.val.take n.val ⦄ := by
  change loop (trimBody n) items ⦃ after => after.val = items.val.take n.val ⦄
  exact trim_spec n items

@[step] theorem rollback_loop5 {M : Type} (items : alloc.vec.Vec (runtime.store.MemInst M)) (n : Usize) :
    runtime.store.instantiate.Store.instantiate_with_loop5 items n ⦃ after =>
      after.val = items.val.take n.val ⦄ := by
  change loop (trimBody n) items ⦃ after => after.val = items.val.take n.val ⦄
  exact trim_spec n items

@[step] theorem rollback_loop6 (items : alloc.vec.Vec (runtime.store.GlobalInst)) (n : Usize) :
    runtime.store.instantiate.Store.instantiate_with_loop6 items n ⦃ after =>
      after.val = items.val.take n.val ⦄ := by
  change loop (trimBody n) items ⦃ after => after.val = items.val.take n.val ⦄
  exact trim_spec n items

@[step] theorem rollback_loop7 (items : alloc.vec.Vec (Itasca.wasm_types.FuncType)) (n : Usize) :
    runtime.store.instantiate.Store.instantiate_with_loop7 items n ⦃ after =>
      after.val = items.val.take n.val ⦄ := by
  change loop (trimBody n) items ⦃ after => after.val = items.val.take n.val ⦄
  exact trim_spec n items

/-- The first rollback loop returns the remaining store fields together with
exactly the retained element-instance prefix. -/
@[step] theorem rollback_elements {M : Type} (s : runtime.store.Store M) (n : Usize) :
    runtime.store.instantiate.Store.instantiate_with_loop0 s n ⦃ after =>
      after = (s.id, s.limits, s.funcs, s.types, s.tables, s.memories, s.globals,
        s.instances, alloc.vec.Vec.from (s.elems.val.take n.val) (by
          have h := s.elems.property
          simp only [List.length_take]
          omega), s.datas, s.externs, s.instance_items) ⦄ := by
  unfold runtime.store.instantiate.Store.instantiate_with_loop0
  apply loop.spec_decr_nat (fun state => state.elems.length)
    (fun state => state.id = s.id ∧ state.limits = s.limits ∧
      state.funcs = s.funcs ∧ state.types = s.types ∧ state.tables = s.tables ∧
      state.memories = s.memories ∧ state.globals = s.globals ∧
      state.instances = s.instances ∧ state.elems.val.take n.val = s.elems.val.take n.val ∧
      state.datas = s.datas ∧ state.externs = s.externs ∧ state.instance_items = s.instance_items)
  · intro state hinv
    unfold runtime.store.instantiate.Store.instantiate_with_loop0.body
    dsimp only
    split
    · rename_i hmore
      have hlt : n.val < state.elems.val.length := by scalar_tac
      simp [alloc.vec.Vec.pop, alloc.vec.Vec.length]
      rcases hinv with ⟨hi, hl, hf, ht, hta, hm, hg, hinst, he, hd, hx, hii⟩
      refine ⟨hi, hl, hf, ht, hta, hm, hg, hinst, ?_, hd, hx, hii, by omega⟩
      simpa only [List.dropLast_eq_take, List.take_take,
        Nat.min_eq_left (by omega : n.val ≤ state.elems.val.length - 1)] using he
    · rename_i hstop
      have hle : state.elems.length ≤ n.val := by scalar_tac
      rcases hinv with ⟨hi, hl, hf, ht, hta, hm, hg, hinst, he, hd, hx, hii⟩
      have heq : state.elems = alloc.vec.Vec.from (s.elems.val.take n.val) (by
          have h := s.elems.property
          simp only [List.length_take]
          omega) := by
        apply alloc.vec.Vec.ext
        simpa only [List.take_of_length_le hle, alloc.vec.Vec.from_val] using he
      simp [hi, hl, hf, ht, hta, hm, hg, hinst, heq, hd, hx, hii]
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Before the commit point, provisional objects extend existing vectors without
changing their retained prefixes. Counters restored by the wrapper are deliberately
absent. This is a staging relation, not a successful-store invariant. -/
structure StagedPrefix {M : Type} (before after : runtime.store.Store M) : Prop where
  identity : after.id = before.id
  limits : after.limits = before.limits
  funcs : after.funcs.val.take before.funcs.length = before.funcs.val
  types : after.types.val.take before.types.length = before.types.val
  tables : after.tables.val.take before.tables.length = before.tables.val
  memories : after.memories.val.take before.memories.length = before.memories.val
  globals : after.globals.val.take before.globals.length = before.globals.val
  instances : after.instances.val.take before.instances.length = before.instances.val
  elems : after.elems.val.take before.elems.length = before.elems.val
  datas : after.datas.val.take before.datas.length = before.datas.val
  externs : after.externs = before.externs
  instanceItems : after.instance_items = before.instance_items

/-- The actual public wrapper restores the exact original raw store after an
uncommitted inner error whose provisional state preserves existing prefixes.
The inner-stage proof must supply `StagedPrefix`; this lemma does not assume
instantiation succeeds or that partially assembled instances satisfy `Shape`. -/
theorem instantiate_rollback {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (platform : runtime.platform.Platform P M)
    (float : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (s staged : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (p p' : P) (error : runtime.ExecError)
    (hprefix : StagedPrefix s staged)
    (hinner : runtime.store.instantiate.Store.instantiate_inner memory platform float allocator
      s module imports p false = .ok (.Err error, staged, p', false)) :
    runtime.store.instantiate.Store.instantiate_with memory platform float allocator s module imports p
      ⦃ answer after p'' => answer = .Err error ∧ after = s ∧ p'' = p' ⦄ := by
  unfold runtime.store.instantiate.Store.instantiate_with
  rw [hinner]
  simp only [bind_ok, runtime.store.instantiation_failed]
  simp
  step with rollback_elements staged (alloc.vec.Vec.len s.elems) 
  subst_vars
  step as ⟨datas, hd⟩
  step as ⟨instances, hi⟩
  step as ⟨funcs, hf⟩
  step as ⟨tables, ht⟩
  step as ⟨memories, hm⟩
  step as ⟨globals, hg⟩
  step as ⟨types, hty⟩
  have hd' : datas = s.datas := by
    apply alloc.vec.Vec.ext
    simpa using hd.trans hprefix.datas
  have hi' : instances = s.instances := by
    apply alloc.vec.Vec.ext
    simpa using hi.trans hprefix.instances
  have hf' : funcs = s.funcs := by
    apply alloc.vec.Vec.ext
    simpa using hf.trans hprefix.funcs
  have ht' : tables = s.tables := by
    apply alloc.vec.Vec.ext
    simpa using ht.trans hprefix.tables
  have hm' : memories = s.memories := by
    apply alloc.vec.Vec.ext
    simpa using hm.trans hprefix.memories
  have hg' : globals = s.globals := by
    apply alloc.vec.Vec.ext
    simpa using hg.trans hprefix.globals
  have hty' : types = s.types := by
    apply alloc.vec.Vec.ext
    simpa using hty.trans hprefix.types
  have he' : alloc.vec.Vec.from (staged.elems.val.take s.elems.length) (by
      have h := staged.elems.property
      simp only [List.length_take]
      omega) = s.elems := by
    apply alloc.vec.Vec.ext
    simpa using hprefix.elems
  simp [hd', hi', hf', ht', hm', hg', hty', he', hprefix.identity,
    hprefix.limits, hprefix.externs, hprefix.instanceItems]

end Itasca.Runtime.Store

end
