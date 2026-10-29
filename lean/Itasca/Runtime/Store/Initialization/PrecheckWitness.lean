import Itasca.Runtime.Store.Initialization.PrecheckErrors

/-!
Independent initializer-precheck witnesses through the validation loop. The construction is used before returning the resolved start handle; it does not invoke the start function.
-/

/-! ## Precheck Witness -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- An actual active element offset resolves beyond its actual target table.
The expression, local target map, store target, and payload are retained. -/
def ElementBoundsFailure {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) : Prop :=
  ∃ (index : Usize) (segment : Itasca.module.Element) (target : U32)
      (offset : Itasca.types.ConstExpr) (words : List U64) (address : runtime.TableAddr)
      (table : runtime.store.TableInst),
    inst.module.module.env.elements.val[index.val]? = some segment ∧
    segment.mode = .Active target offset ∧
    Interp.InitializerResolution store inst offset .I32 words ∧
    inst.tables.val[target.val]? = some address ∧
    store.tables.val[address.index.val]? = some table ∧
    table.elements.length < ((words[0]?).getD 0#u64).val % 2^32 + segment.init.length

/-- The corresponding exact source-offset witness for an active data segment. -/
def DataBoundsFailure {M : Type} (view : M → Slice U8) (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) : Prop :=
  ∃ (index : Usize) (segment : Itasca.module.Data) (target : U32)
      (offset : Itasca.types.ConstExpr) (words : List U64) (address : runtime.MemoryAddr)
      (memory : runtime.store.MemInst M),
    inst.module.module.tail.data.val[index.val]? = some segment ∧
    segment.mode = .Active target offset ∧
    Interp.InitializerResolution store inst offset .I32 words ∧
    inst.memories.val[target.val]? = some address ∧
    store.memories.val[address.index.val]? = some memory ∧
    (view memory.buf).length < ((words[0]?).getD 0#u64).val % 2^32 + segment.init.length

def PrecheckCause {M : Type} (view : M → Slice U8) (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (error : runtime.ExecError) : Prop :=
  ResourceError error ∨
  (error = .Trap .TableOutOfBounds ∧ ElementBoundsFailure store inst) ∨
  (error = .Trap .MemoryOutOfBounds ∧ DataBoundsFailure view store inst)

theorem PrecheckCause.precommit {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {inst error} (cause : PrecheckCause view store inst error) :
    PrecommitError .Wasm1 error := by
  rcases cause with resource | ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact resource.precommit
  · rfl
  · rfl

/-- If a rejected precommit computation reports a trap, a retained active
source segment and resolved target explain its precise bounds failure. -/
def PrecommitBoundsEvidence {M : Type} (view : M → Slice U8) (store : runtime.store.Store M)
    (module : runtime.compiler.ExecutableModule) (error : runtime.ExecError) : Prop :=
  ∀ trap, error = .Trap trap → ∃ (index : Usize) (inst : runtime.store.ModuleInst),
    store.instances.val[index.val]? = some inst ∧ inst.module = module ∧
    PrecheckCause view store inst error

end Itasca.Runtime.Store

end

/-! ## Precheck Witness Loops -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)
theorem element_bounds_ready_witness (law : Platform.AllocCorrect allocator) (view : M → Slice U8)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.ModuleInst) (segment : Itasca.module.Element)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (helem : inst.module.module.env.elements.val[index.val]? = some segment)
    (ready : ElementPrecheckReady store inst index segment)
    (bindings : InitializerBindings store inst) :
    runtime.store.instantiate.Store.check_element_bounds memory hooks floats allocator store platform instIndex index
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧ ErrorAllowed (PrecheckCause view store inst) out.1 ⦄ := by
  cases mode : segment.mode with
  | Active tableIndex offset =>
    simp only [ElementPrecheckReady, mode] at ready
    obtain ⟨function, code, words, addr, table, mapping, hc, compiled, resolved, ht, htable⟩ := ready
    apply WP.spec_mono (element_bounds_active_errors memory hooks floats allocator law store platform instIndex index inst segment
      tableIndex offset function code words addr table hi helem mode mapping hc compiled resolved bindings ht htable)
    rintro ⟨result, after, host⟩ ⟨sameStore, sameHost, errors⟩
    refine ⟨sameStore, sameHost, ?_⟩
    cases result with
    | Ok value => trivial
    | Err error =>
      rcases errors error rfl with resource | ⟨rfl, outside⟩
      · exact Or.inl resource
      · exact Or.inr (Or.inl ⟨rfl, index, segment, tableIndex, offset, words, addr, table,
          helem, mode, resolved, ht, htable, outside⟩)
  | Passive =>
    apply WP.spec_mono (element_bounds_inactive memory hooks floats allocator store platform instIndex index
      inst segment hi helem (.inl mode))
    rintro out rfl
    exact ⟨rfl, rfl, trivial⟩
  | Declarative =>
    apply WP.spec_mono (element_bounds_inactive memory hooks floats allocator store platform instIndex index
      inst segment hi helem (.inr mode))
    rintro out rfl
    exact ⟨rfl, rfl, trivial⟩

theorem data_bounds_ready_witness (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (memoryLaws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.ModuleInst) (segment : Itasca.module.Data)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hdata : inst.module.module.tail.data.val[index.val]? = some segment)
    (ready : DataPrecheckReady store inst index segment)
    (bindings : InitializerBindings store inst) :
    runtime.store.instantiate.Store.check_data_bounds memory hooks floats allocator store platform instIndex index
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧ ErrorAllowed (PrecheckCause view store inst) out.1 ⦄ := by
  cases mode : segment.mode with
  | Active memoryIndex offset =>
    simp only [DataPrecheckReady, mode] at ready
    obtain ⟨function, code, words, addr, mem, mapping, hc, compiled, resolved, hm, hmemory⟩ := ready
    apply WP.spec_mono (data_bounds_active_errors memory hooks floats allocator law view memoryLaws store platform instIndex index
      inst segment memoryIndex offset function code words addr mem hi hdata mode mapping hc compiled resolved bindings hm hmemory)
    rintro ⟨result, after, host⟩ ⟨sameStore, sameHost, errors⟩
    refine ⟨sameStore, sameHost, ?_⟩
    cases result with
    | Ok value => trivial
    | Err error =>
      rcases errors error rfl with resource | ⟨rfl, outside⟩
      · exact Or.inl resource
      · exact Or.inr (Or.inr ⟨rfl, index, segment, memoryIndex, offset, words, addr, mem,
          hdata, mode, resolved, hm, hmemory, outside⟩)
  | Passive =>
    apply WP.spec_mono (data_bounds_inactive memory hooks floats allocator store platform instIndex index
      inst segment hi hdata mode)
    rintro out rfl
    exact ⟨rfl, rfl, trivial⟩

theorem element_precheck_loop_witness (law : Platform.AllocCorrect allocator) (view : M → Slice U8)
    (store : runtime.store.Store M) (platform : P) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (allowed : ErrorAllowed (PrecheckCause view store inst) status)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (bindings : InitializerBindings store inst)
    (certificates : ∀ index : Usize, index.val < inst.module.module.env.elements.length →
      ∃ segment, inst.module.module.env.elements.val[index.val]? = some segment ∧
        ElementPrecheckReady store inst index segment)
    (hstart : start.val ≤ inst.module.module.env.elements.length) :
    runtime.store.instantiate.Store.prepare_instance_loop10 memory hooks floats allocator store platform status start instIndex
      ⦃ out => ∃ finalStatus, out = storeParts store platform finalStatus ∧ ErrorAllowed (PrecheckCause view store inst) finalStatus ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop10
  apply loop.spec_decr_nat (fun state => inst.module.module.env.elements.length - state.2.2.2.val)
    (fun state => state.1 = store ∧ state.2.1 = platform ∧
      state.2.2.2.val ≤ inst.module.module.env.elements.length ∧
      ErrorAllowed (PrecheckCause view store inst) state.2.2.1)
  · rintro ⟨current, host, state, index⟩ ⟨hcurrent, hhost, hindex, hallowed⟩
    dsimp only at hcurrent hhost hindex hallowed ⊢
    subst current host
    unfold runtime.store.instantiate.Store.prepare_instance_loop10.body
    step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
    subst found
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.module.Module.impl.env, Itasca.module.Env.impl.elements, bind_ok]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.env.elements.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases state with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨_, rfl, hallowed⟩
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        obtain ⟨segment, helem, ready⟩ := certificates index hmore
        step with element_bounds_ready_witness memory hooks floats allocator law view store platform instIndex index
          inst segment hi helem ready bindings as ⟨result, after, host', hs, hp, errors⟩
        subst after host'
        cases result <;> step as ⟨next, hnext⟩ <;> exact ⟨by omega, errors, by omega⟩
    · simp only [WP.spec_ok]
      exact ⟨_, rfl, hallowed⟩
  · exact ⟨rfl, rfl, hstart, allowed⟩

theorem data_precheck_loop_witness (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (memoryLaws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (platform : P) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (allowed : ErrorAllowed (PrecheckCause view store inst) status)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (bindings : InitializerBindings store inst)
    (certificates : ∀ index : Usize, index.val < inst.module.module.tail.data.length →
      ∃ segment, inst.module.module.tail.data.val[index.val]? = some segment ∧
        DataPrecheckReady store inst index segment)
    (hstart : start.val ≤ inst.module.module.tail.data.length) :
    runtime.store.instantiate.Store.prepare_instance_loop11 memory hooks floats allocator store platform status start instIndex
      ⦃ out => ∃ finalStatus, out = storeParts store platform finalStatus ∧ ErrorAllowed (PrecheckCause view store inst) finalStatus ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop11
  apply loop.spec_decr_nat (fun state => inst.module.module.tail.data.length - state.2.2.2.val)
    (fun state => state.1 = store ∧ state.2.1 = platform ∧
      state.2.2.2.val ≤ inst.module.module.tail.data.length ∧
      ErrorAllowed (PrecheckCause view store inst) state.2.2.1)
  · rintro ⟨current, host, state, index⟩ ⟨hcurrent, hhost, hindex, hallowed⟩
    dsimp only at hcurrent hhost hindex hallowed ⊢
    subst current host
    unfold runtime.store.instantiate.Store.prepare_instance_loop11.body
    step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
    subst found
    simp only [runtime.compiler.ExecutableModule.tail,
      Itasca.module.Module.impl.tail, bind_ok]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.tail.data.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases state with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨_, rfl, hallowed⟩
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        obtain ⟨segment, helem, ready⟩ := certificates index hmore
        step with data_bounds_ready_witness memory hooks floats allocator law view memoryLaws store platform instIndex index
          inst segment hi helem ready bindings as ⟨result, after, host', hs, hp, errors⟩
        subst after host'
        cases result <;> step as ⟨next, hnext⟩ <;> exact ⟨by omega, errors, by omega⟩
    · simp only [WP.spec_ok]
      exact ⟨_, rfl, hallowed⟩
  · exact ⟨rfl, rfl, hstart, allowed⟩

end Itasca.Runtime.Store

end
