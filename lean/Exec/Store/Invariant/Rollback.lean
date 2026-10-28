import Exec.Representation.StoreInvariant

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

@[step] theorem rollback_loop7 (items : alloc.vec.Vec (Itasca.types.FuncType)) (n : Usize) :
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
