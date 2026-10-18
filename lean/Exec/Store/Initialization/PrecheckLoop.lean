import Exec.Store.Initialization.Precheck

/-! Structural readiness and finite execution of the Wasm1 precommit bounds
passes. Certificates describe source modes, offset code, and issued addresses. -/
namespace Exec.Store
open Aeneas Aeneas.Std

def ElementPrecheckReady {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.Instance) (index : Usize) (segment : Itasca.module.Element) : Prop :=
  match segment.mode with
  | .Active tableIndex offset => ∃ function code words addr table,
      inst.module.element_offsets.val[index.val]? = some (some function) ∧
      inst.module.functions.val[function.val]? = some code ∧
      Code.InitializerCode code offset .I32 ∧
      Interp.InitializerResolution store inst offset .I32 words ∧
      inst.tables.val[tableIndex.val]? = some addr ∧ store.tables.val[addr.index.val]? = some table
  | _ => True

def DataPrecheckReady {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.Instance) (index : Usize) (segment : Itasca.module.Data) : Prop :=
  match segment.mode with
  | .Active memoryIndex offset => ∃ function code words addr mem,
      inst.module.data_offsets.val[index.val]? = some (some function) ∧
      inst.module.functions.val[function.val]? = some code ∧
      Code.InitializerCode code offset .I32 ∧
      Interp.InitializerResolution store inst offset .I32 words ∧
      inst.memories.val[memoryIndex.val]? = some addr ∧ store.memories.val[addr.index.val]? = some mem
  | _ => True

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem element_range_ready (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.Instance) (segment : Itasca.module.Element)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (helem : inst.module.module.env.elements.val[index.val]? = some segment)
    (ready : ElementPrecheckReady store inst index segment)
    (bindings : InitializerBindings store inst) :
    runtime.store.instantiate.Store.element_range_for memory hooks floats allocator store platform instIndex index
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ⦄ := by
  cases mode : segment.mode with
  | Active tableIndex offset =>
    simp only [ElementPrecheckReady, mode] at ready
    obtain ⟨function, code, words, addr, table, mapping, hc, compiled, resolved, ht, htable⟩ := ready
    exact element_range_active memory hooks floats allocator law store platform instIndex index inst segment
      tableIndex offset function code words addr table hi helem mode mapping hc compiled resolved bindings ht htable
  | Passive =>
    apply WP.spec_mono (element_range_inactive memory hooks floats allocator store platform instIndex index
      inst segment hi helem (.inl mode))
    rintro out rfl
    exact ⟨rfl, rfl⟩
  | Declarative =>
    apply WP.spec_mono (element_range_inactive memory hooks floats allocator store platform instIndex index
      inst segment hi helem (.inr mode))
    rintro out rfl
    exact ⟨rfl, rfl⟩

theorem data_range_ready (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (memoryLaws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.Instance) (segment : Itasca.module.Data)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hdata : inst.module.module.tail.data.val[index.val]? = some segment)
    (ready : DataPrecheckReady store inst index segment)
    (bindings : InitializerBindings store inst) :
    runtime.store.instantiate.Store.data_range_for memory hooks floats allocator store platform instIndex index
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ⦄ := by
  cases mode : segment.mode with
  | Active memoryIndex offset =>
    simp only [DataPrecheckReady, mode] at ready
    obtain ⟨function, code, words, addr, mem, mapping, hc, compiled, resolved, hm, hmemory⟩ := ready
    exact data_range_active memory hooks floats allocator law view memoryLaws store platform instIndex index
      inst segment memoryIndex offset function code words addr mem hi hdata mode mapping hc compiled resolved bindings hm hmemory
  | Passive =>
    apply WP.spec_mono (data_range_inactive memory hooks floats allocator store platform instIndex index
      inst segment hi hdata mode)
    rintro out rfl
    exact ⟨rfl, rfl⟩

def storeParts {M P : Type} (store : runtime.store.Store M) (platform : P)
    (status : core.result.Result Unit runtime.ExecError) :=
  (store.id, store.limits, store.funcs, store.types, store.tables, store.memories,
    store.globals, store.instances, store.elems, store.datas, store.externs,
    store.instance_items, store.signature_values, store.memory_bytes, store.table_elements,
    platform, status)

theorem element_precheck_loop (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex start : Usize)
    (inst : runtime.store.Instance) (status : core.result.Result Unit runtime.ExecError)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (bindings : InitializerBindings store inst)
    (certificates : ∀ index : Usize, index.val < inst.module.module.env.elements.length →
      ∃ segment, inst.module.module.env.elements.val[index.val]? = some segment ∧
        ElementPrecheckReady store inst index segment)
    (hstart : start.val ≤ inst.module.module.env.elements.length) :
    runtime.store.instantiate.Store.instantiate_inner_loop10 memory hooks floats allocator store platform status start instIndex
      ⦃ out => ∃ finalStatus, out = storeParts store platform finalStatus ⦄ := by
  unfold runtime.store.instantiate.Store.instantiate_inner_loop10
  apply loop.spec_decr_nat (fun state => inst.module.module.env.elements.length - state.2.2.2.val)
    (fun state => state.1 = store ∧ state.2.1 = platform ∧
      state.2.2.2.val ≤ inst.module.module.env.elements.length)
  · rintro ⟨current, host, state, index⟩ ⟨hcurrent, hhost, hindex⟩
    dsimp only at hcurrent hhost hindex ⊢
    subst current host
    unfold runtime.store.instantiate.Store.instantiate_inner_loop10.body
    step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
    subst found
    simp only [runtime.compiler.ExecutableModule.env, module.Module.env,
      Itasca.module.Module.impl.env, module.Env.elements, Itasca.module.Env.impl.elements, bind_ok]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.env.elements.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases state with
      | Err error =>
        simp [core.result.Result.is_ok, storeParts]
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        obtain ⟨segment, helem, ready⟩ := certificates index hmore
        step with element_range_ready memory hooks floats allocator law store platform instIndex index
          inst segment hi helem ready bindings as ⟨result, after, host', hs, hp⟩
        subst after host'
        cases result <;> step as ⟨next, hnext⟩ <;> constructor <;> omega
    · simp [storeParts]
  · exact ⟨rfl, rfl, hstart⟩

theorem data_precheck_loop (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (memoryLaws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (platform : P) (instIndex start : Usize)
    (inst : runtime.store.Instance) (status : core.result.Result Unit runtime.ExecError)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (bindings : InitializerBindings store inst)
    (certificates : ∀ index : Usize, index.val < inst.module.module.tail.data.length →
      ∃ segment, inst.module.module.tail.data.val[index.val]? = some segment ∧
        DataPrecheckReady store inst index segment)
    (hstart : start.val ≤ inst.module.module.tail.data.length) :
    runtime.store.instantiate.Store.instantiate_inner_loop11 memory hooks floats allocator store platform status start instIndex
      ⦃ out => ∃ finalStatus, out = storeParts store platform finalStatus ⦄ := by
  unfold runtime.store.instantiate.Store.instantiate_inner_loop11
  apply loop.spec_decr_nat (fun state => inst.module.module.tail.data.length - state.2.2.2.val)
    (fun state => state.1 = store ∧ state.2.1 = platform ∧
      state.2.2.2.val ≤ inst.module.module.tail.data.length)
  · rintro ⟨current, host, state, index⟩ ⟨hcurrent, hhost, hindex⟩
    dsimp only at hcurrent hhost hindex ⊢
    subst current host
    unfold runtime.store.instantiate.Store.instantiate_inner_loop11.body
    step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
    subst found
    simp only [runtime.compiler.ExecutableModule.tail, module.Module.tail,
      Itasca.module.Module.impl.tail, bind_ok]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.tail.data.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases state with
      | Err error =>
        simp [core.result.Result.is_ok, storeParts]
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        obtain ⟨segment, helem, ready⟩ := certificates index hmore
        step with data_range_ready memory hooks floats allocator law view memoryLaws store platform instIndex index
          inst segment hi helem ready bindings as ⟨result, after, host', hs, hp⟩
        subst after host'
        cases result <;> step as ⟨next, hnext⟩ <;> constructor <;> omega
    · simp [storeParts]
  · exact ⟨rfl, rfl, hstart⟩

end Exec.Store
