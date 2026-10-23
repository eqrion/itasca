import Exec.Store.Invariant.Rollback
import Exec.Store.Api.DefineTable
import Exec.Store.Invariant.InternTypes

namespace Exec.Store
open Aeneas Aeneas.Std

theorem StagedPrefix.refl {M : Type} (s : runtime.store.Store M) : StagedPrefix s s := by
  constructor <;> simp

private theorem prefix_trans {T : Type} (a b c : List T)
    (hab : b.take a.length = a) (hbc : c.take b.length = b) : c.take a.length = a := by
  have hlen : a.length ≤ b.length := by
    have h := congrArg List.length hab
    simp only [List.length_take] at h
    omega
  have h := congrArg (List.take a.length) hbc
  simpa [List.take_take, Nat.min_eq_left hlen, hab] using h

theorem StagedPrefix.trans {M : Type} {a b c : runtime.store.Store M}
    (hab : StagedPrefix a b) (hbc : StagedPrefix b c) : StagedPrefix a c where
  identity := hbc.identity.trans hab.identity
  limits := hbc.limits.trans hab.limits
  funcs := prefix_trans _ _ _ hab.funcs hbc.funcs
  types := prefix_trans _ _ _ hab.types hbc.types
  tables := prefix_trans _ _ _ hab.tables hbc.tables
  memories := prefix_trans _ _ _ hab.memories hbc.memories
  globals := prefix_trans _ _ _ hab.globals hbc.globals
  instances := prefix_trans _ _ _ hab.instances hbc.instances
  elems := prefix_trans _ _ _ hab.elems hbc.elems
  datas := prefix_trans _ _ _ hab.datas hbc.datas
  externs := hbc.externs.trans hab.externs
  instanceItems := hbc.instanceItems.trans hab.instanceItems

/-- Type canonicalization retains all old objects on every ordinary outcome,
including allocation failure. -/
theorem intern_type_staged {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (s : runtime.store.Store M) (ty : Itasca.types.FuncType)
    (hbound : objectCount s ≤ Usize.max) :
    runtime.store.Store.intern_type ops allocator s ty ⦃ result after => StagedPrefix s after ⦄ := by
  apply WP.spec_mono (intern_type_effect ops allocator ha s ty hbound)
  intro result heffect
  rcases heffect with ⟨error, herr⟩ | ⟨index, hindex, hsame⟩ | ⟨types, count, htypes, hnot, hroom, hcount, hlimit, happend⟩
  · simpa [herr] using StagedPrefix.refl s
  · simpa [hsame] using StagedPrefix.refl s
  · rw [happend]
    constructor <;> simp [htypes]

theorem define_table_staged {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (s : runtime.store.Store M) (ty : Itasca.types.TableType)
    (hbound : objectCount s ≤ Usize.max) :
    runtime.store.Store.define_table_with ops allocator s ty ⦃ result after => StagedPrefix s after ⦄ := by
  apply WP.spec_mono (define_table_effect ops allocator ha s ty hbound)
  intro result heffect
  rcases heffect with ⟨error, herr⟩ | ⟨tables, elements, count, helements, htables, hfit, hroom, hcount, hlimit, happend⟩
  · simpa [herr] using StagedPrefix.refl s
  · rw [happend]
    constructor <;> simp [htables]

theorem define_memory_staged {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view)
    (s : runtime.store.Store M) (ty : Itasca.types.MemType) (buffer : M)
    (hbound : objectCount s ≤ Usize.max) :
    runtime.store.Store.define_memory_with ops allocator s ty buffer ⦃ result after => StagedPrefix s after ⦄ := by
  apply WP.spec_mono (define_memory_effect ops allocator ha view laws s ty buffer hbound)
  intro result heffect
  rcases heffect with ⟨error, herr⟩ | ⟨memories, count, hmemories, hfit, hsize, hroom, hcount, hlimit, happend⟩
  · simpa [herr] using StagedPrefix.refl s
  · rw [happend]
    constructor <;> simp [hmemories]

theorem define_global_staged {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (s : runtime.store.Store M) (ty : Itasca.types.GlobalType) (value : runtime.Value)
    (hbound : objectCount s ≤ Usize.max) (htype : ty.valtype = Interp.rawType value)
    (hv : ValueInStore s value) :
    runtime.store.Store.define_global_with ops allocator s ty value ⦃ result after => StagedPrefix s after ⦄ := by
  apply WP.spec_mono (define_global_effect ops allocator ha s ty value hbound htype hv)
  intro result heffect
  rcases heffect with ⟨error, herr⟩ | ⟨globals, words, hencode, hglobals, hroom, happend⟩
  · simpa [herr] using StagedPrefix.refl s
  · rw [happend]
    constructor <;> simp [hglobals]

theorem add_instance_type_staged {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (s : runtime.store.Store M) (inst : runtime.store.ModuleInst) (i : Usize)
    (hbound : objectCount s ≤ Usize.max)
    (hi : i.val < inst.module.module.env.types.length)
    (hroom : inst.types.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_type ops allocator s inst i
      ⦃ _ after _ => StagedPrefix s after ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_type
  simp only [runtime.compiler.ExecutableModule.env, module.Module.env,
    Itasca.module.Module.impl.env, module.Env.types, Itasca.module.Env.impl.types, bind_ok]
  have hb : i.val < inst.module.module.env.types.deref.length := by simpa [alloc.vec.Vec.deref] using hi
  step as ⟨ty, hty⟩
  step with intern_type_staged ops allocator ha s ty hbound as ⟨answer, after, hafter⟩
  cases answer
  · simp [core.result.Result.Insts.CoreOpsTry.branch]
    step as ⟨types, htypes⟩
    exact hafter
  · simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using hafter

theorem add_instance_table_staged {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (s : runtime.store.Store M) (inst : runtime.store.ModuleInst) (i : Usize)
    (hbound : objectCount s ≤ Usize.max)
    (hi : i.val < inst.module.module.env.table_types.length)
    (hroom : inst.tables.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_table ops allocator s inst i
      ⦃ _ after _ => StagedPrefix s after ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_table
  simp only [runtime.compiler.ExecutableModule.env, module.Module.env,
    Itasca.module.Module.impl.env, module.Env.table_types, Itasca.module.Env.impl.table_types, bind_ok]
  have hb : i.val < inst.module.module.env.table_types.deref.length := by simpa [alloc.vec.Vec.deref] using hi
  step as ⟨ty, hty⟩
  step with define_table_staged ops allocator ha s ty hbound as ⟨answer, after, hafter⟩
  cases answer
  · simp [core.result.Result.Insts.CoreOpsTry.branch]
    step as ⟨tables, htables⟩
    exact hafter
  · simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using hafter

theorem add_instance_memory_staged {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view)
    (s : runtime.store.Store M) (inst : runtime.store.ModuleInst) (i : Usize)
    (hbound : objectCount s ≤ Usize.max)
    (hi : i.val < inst.module.module.env.mem_types.length)
    (hroom : inst.memories.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_memory ops allocator s inst i
      ⦃ _ after _ => StagedPrefix s after ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_memory
  simp only [runtime.compiler.ExecutableModule.env, module.Module.env,
    Itasca.module.Module.impl.env, module.Env.mem_types, Itasca.module.Env.impl.mem_types, bind_ok]
  have hb : i.val < inst.module.module.env.mem_types.deref.length := by simpa [alloc.vec.Vec.deref] using hi
  step as ⟨ty, hty⟩
  step as ⟨minimum, hminimum⟩
  step as ⟨bytes, hbytes⟩
  step as ⟨maximum, hmaximum⟩
  split
  · simpa using StagedPrefix.refl s
  · rename_i hfits
    step as ⟨size, hsize⟩
    step with within_spec s.memory_bytes size s.limits.max_memory_bytes as ⟨fits, hfit⟩
    cases fits
    · simpa using StagedPrefix.refl s
    · simp
      step as ⟨size', hsize'⟩
      step with laws.create size' as ⟨buffer, hbuffer⟩
      cases buffer with
      | none => simpa using StagedPrefix.refl s
      | some memory =>
        simp
        step with define_memory_staged ops allocator ha view laws s ty memory hbound as ⟨answer, after, hafter⟩
        cases answer
        · simp [core.result.Result.Insts.CoreOpsTry.branch]
          step as ⟨memories, hmemories⟩
          exact hafter
        · simpa [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using hafter

/-- Defining a function may point at the not-yet-published instance; staging
requires only unchanged retained prefixes, not a false complete-store shape. -/
theorem add_instance_function_staged {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (s : runtime.store.Store M) (inst : runtime.store.ModuleInst) (instanceIndex i : Usize)
    (hbound : objectCount s ≤ Usize.max)
    (hi : i.val < inst.module.module.env.func_type_indices.length)
    (htype : (inst.module.module.env.func_type_indices.val[i.val]).val < inst.types.length)
    (hroom : inst.funcs.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_function ops allocator s inst instanceIndex i
      ⦃ _ after _ => StagedPrefix s after ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_function
  step with room_spec ops s hbound as ⟨room, hroomResult⟩
  rw [hroomResult]
  split
  · rename_i hspace
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    obtain ⟨answer, hr⟩ := reserve_wrapper_eq allocator ha s.funcs 1#usize
    rw [hr]
    cases answer
    · simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using StagedPrefix.refl s
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        runtime.compiler.ExecutableModule.env, module.Module.env,
        Itasca.module.Module.impl.env, module.Env.func_type_indices,
        Itasca.module.Env.impl.func_type_indices]
      have hb : i.val < inst.module.module.env.func_type_indices.deref.length := by
        simpa [alloc.vec.Vec.deref] using hi
      step as ⟨sourceType, hsourceType⟩
      step as ⟨typeIndex, htypeIndex⟩
      have ht : typeIndex.val < inst.types.length := by
        simpa [htypeIndex, hsourceType, alloc.vec.Vec.deref] using htype
      step as ⟨signature, hsignature⟩
      have hfuncroom : s.funcs.length < Usize.max := by
        unfold objectCount at hspace
        scalar_tac
      step as ⟨functions, hfunctions⟩
      step as ⟨addresses, haddresses⟩
      constructor <;> simp [hfunctions]
  · simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using StagedPrefix.refl s

end Exec.Store
