import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Store.Initialization.PrecheckLoop
import Itasca.Runtime.Store.Initialization.InitializerResourceCauses
import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Store.Initialization.PrecheckWitness

/-!
Precheck resource causes and their loop transport. The construction is used before returning the resolved start handle; it does not invoke the start function.
-/

/-! ## Precheck Resource Causes -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

private theorem value_i32_eq (value : runtime.Value) (typed : Interp.rawType value = .I32) :
    ∃ bits, runtime.Value.i32 value = .ok (.Ok bits) := by
  cases value <;> simp_all [Interp.rawType, runtime.Value.i32]

private theorem value_i32_bits (value : runtime.Value) (bits : U32) (lo hi : U64)
    (read : runtime.Value.i32 value = .ok (.Ok bits))
    (decoded : Interp.sourceValue value = decodeWords .I32 lo hi) : bits.val = lo.val % 2^32 := by
  cases value <;> simp_all [runtime.Value.i32, Interp.sourceValue, decodeWords]

private theorem range_error (start len : U64) (size : Usize) (trap : runtime.Trap) (error : runtime.ExecError)
    (effect : Interp.RangeEffect start len size trap (.Err error)) :
    error = .Trap trap ∧ size.val < start.val + len.val := by
  unfold Interp.RangeEffect at effect
  split at effect
  · obtain ⟨range, impossible, _⟩ := effect
    cases impossible
  · exact ⟨core.result.Result.Err.inj effect, by omega⟩

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem element_bounds_active_resource_causes (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.ModuleInst) (segment : Itasca.module.Element)
    (tableIndex : U32) (offset : Itasca.types.ConstExpr) (function : Usize)
    (code : runtime.bytecode.CompiledFunction) (words : List U64)
    (addr : runtime.TableAddr) (table : runtime.store.TableInst)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (helem : inst.module.module.env.elements.val[index.val]? = some segment)
    (active : segment.mode = .Active tableIndex offset)
    (mapping : inst.module.element_offsets.val[index.val]? = some (some function))
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Code.InitializerCode code offset .I32)
    (resolved : Interp.InitializerResolution store inst offset .I32 words)
    (bindings : InitializerBindings store inst)
    (ht : inst.tables.val[tableIndex.val]? = some addr)
    (htable : store.tables.val[addr.index.val]? = some table) :
    runtime.store.instantiate.Store.check_element_bounds memory hooks floats allocator store platform instIndex index
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧
        ∀ error, out.1 = .Err error → Interp.SyntheticPreparationCause allocator store code error ∨
          (error = .Trap .TableOutOfBounds ∧ table.elements.length < ((words[0]?).getD 0#u64).val % 2^32 + segment.init.length) ⦄ := by
  unfold runtime.store.instantiate.Store.check_element_bounds
  step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.module.Module.impl.env, Itasca.module.Env.impl.elements, bind_ok]
  step with Itasca.Runtime.Representation.slice_index_given inst.module.module.env.elements.deref index segment
    (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
  subst found
  rw [active]
  step with Interp.vec_index_given inst.module.element_offsets index (some function) mapping
    as ⟨found, hfound⟩
  subst found
  step with eval_const_resource_causes memory hooks floats allocator law store platform instIndex function
    inst code offset .I32 words hi hc compiled resolved (by simp)
    as ⟨result, after, host, hs, hp, hvalue, errors⟩
  subst after host
  cases result with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
    exact ⟨True.intro, True.intro, fun e equal => by cases equal; exact Or.inl (errors error rfl)⟩
  | Ok value =>
    obtain ⟨bits, hbits⟩ := value_i32_eq value (hvalue value rfl).1
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hbits]
    step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
    subst found
    step with Itasca.Runtime.Representation.slice_index_given inst.module.module.env.elements.deref index segment
      (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
    subst found
    simp only [lift, bind_ok]
    step with Interp.vec_index_given inst.tables (UScalar.cast .Usize tableIndex) addr
      (by simpa using ht) as ⟨found, hfound⟩
    subst found
    step with Interp.vec_index_given store.tables addr.index table htable as ⟨found, hfound⟩
    subst found
    step with Interp.range_effect (UScalar.cast .U64 bits) (UScalar.cast .U64 segment.init.len)
      table.elements.len .TableOutOfBounds as ⟨checked, hchecked⟩
    cases checked with
    | Ok value => simp [core.result.Result.Insts.CoreOpsTry.branch]
    | Err error =>
      obtain ⟨same, outside⟩ := range_error _ _ _ _ error hchecked
      have bitsEq := value_i32_bits value bits _ _ hbits (hvalue value rfl).2
      have bitsCast : (UScalar.cast .U64 bits).val = bits.val := by scalar_tac
      have rejected : table.elements.length < ((words[0]?).getD 0#u64).val % 2^32 + segment.init.length := by
        simpa [bitsCast, Interp.usize_to_u64_exact, bitsEq] using outside
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
      exact ⟨True.intro, True.intro, fun e equal => by cases equal; exact Or.inr ⟨same, rejected⟩⟩

theorem data_bounds_active_resource_causes (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (memoryLaws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.ModuleInst) (segment : Itasca.module.Data)
    (memoryIndex : U32) (offset : Itasca.types.ConstExpr) (function : Usize)
    (code : runtime.bytecode.CompiledFunction) (words : List U64)
    (addr : runtime.MemoryAddr) (mem : runtime.store.MemInst M)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (helem : inst.module.module.tail.data.val[index.val]? = some segment)
    (active : segment.mode = .Active memoryIndex offset)
    (mapping : inst.module.data_offsets.val[index.val]? = some (some function))
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Code.InitializerCode code offset .I32)
    (resolved : Interp.InitializerResolution store inst offset .I32 words)
    (bindings : InitializerBindings store inst)
    (ht : inst.memories.val[memoryIndex.val]? = some addr)
    (hmemory : store.memories.val[addr.index.val]? = some mem) :
    runtime.store.instantiate.Store.check_data_bounds memory hooks floats allocator store platform instIndex index
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧
        ∀ error, out.1 = .Err error → Interp.SyntheticPreparationCause allocator store code error ∨
          (error = .Trap .MemoryOutOfBounds ∧ (view mem.buf).length < ((words[0]?).getD 0#u64).val % 2^32 + segment.init.length) ⦄ := by
  unfold runtime.store.instantiate.Store.check_data_bounds
  step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [runtime.compiler.ExecutableModule.tail,
    Itasca.module.Module.impl.tail, bind_ok]
  step with Interp.vec_index_given inst.module.module.tail.data index segment helem as ⟨found, hfound⟩
  subst found
  rw [active]
  step with Interp.vec_index_given inst.module.data_offsets index (some function) mapping
    as ⟨found, hfound⟩
  subst found
  step with eval_const_resource_causes memory hooks floats allocator law store platform instIndex function
    inst code offset .I32 words hi hc compiled resolved (by simp)
    as ⟨result, after, host, hs, hp, hvalue, errors⟩
  subst after host
  cases result with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
    exact ⟨True.intro, True.intro, fun e equal => by cases equal; exact Or.inl (errors error rfl)⟩
  | Ok value =>
    obtain ⟨bits, hbits⟩ := value_i32_eq value (hvalue value rfl).1
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hbits]
    step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
    subst found
    step with Interp.vec_index_given inst.module.module.tail.data index segment helem as ⟨found, hfound⟩
    subst found
    simp only [lift, bind_ok]
    step with Interp.vec_index_given inst.memories (UScalar.cast .Usize memoryIndex) addr
      (by simpa using ht) as ⟨found, hfound⟩
    subst found
    step with Interp.vec_index_given store.memories addr.index mem hmemory as ⟨found, hfound⟩
    subst found
    rw [memoryLaws.read mem.buf, bind_ok]
    step with Interp.range_effect (UScalar.cast .U64 bits) (UScalar.cast .U64 segment.init.len)
      (view mem.buf).len .MemoryOutOfBounds as ⟨checked, hchecked⟩
    cases checked with
    | Ok value => simp [core.result.Result.Insts.CoreOpsTry.branch]
    | Err error =>
      obtain ⟨same, outside⟩ := range_error _ _ _ _ error hchecked
      have bitsEq := value_i32_bits value bits _ _ hbits (hvalue value rfl).2
      have bitsCast : (UScalar.cast .U64 bits).val = bits.val := by scalar_tac
      have rejected : (view mem.buf).length < ((words[0]?).getD 0#u64).val % 2^32 + segment.init.length := by
        simpa [bitsCast, Interp.usize_to_u64_exact, bitsEq] using outside
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
      exact ⟨True.intro, True.intro, fun e equal => by cases equal; exact Or.inr ⟨same, rejected⟩⟩

end Itasca.Runtime.Store

end

/-! ## Precheck Resource Loops -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
/-- Synthetic setup failure belongs to an active source-segment offset. -/
def OffsetInitializerCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (error : runtime.ExecError) : Prop :=
  ∃ (index : Usize) (target : U32), ∃ offset function code,
    ((∃ segment, inst.module.module.env.elements.val[index.val]? = some segment ∧
        segment.mode = .Active target offset ∧
        inst.module.element_offsets.val[index.val]? = some (some function)) ∨
      (∃ segment, inst.module.module.tail.data.val[index.val]? = some segment ∧
        segment.mode = .Active target offset ∧
        inst.module.data_offsets.val[index.val]? = some (some function))) ∧
    inst.module.functions.val[function.val]? = some code ∧ Code.InitializerCode code offset .I32 ∧
    Interp.SyntheticPreparationCause allocator store code error

/-- Refined Wasm1 checks retain exact resource requests or generated bounds witnesses. -/
def PrecheckResourceCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (error : runtime.ExecError) : Prop :=
  OffsetInitializerCause allocator store inst error ∨
  (error = .Trap .TableOutOfBounds ∧ ElementBoundsFailure store inst) ∨
  (error = .Trap .MemoryOutOfBounds ∧ DataBoundsFailure view store inst)

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)
theorem element_bounds_ready_resource_causes (law : Platform.AllocCorrect allocator) (view : M → Slice U8)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.ModuleInst) (segment : Itasca.module.Element)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (helem : inst.module.module.env.elements.val[index.val]? = some segment)
    (ready : ElementPrecheckReady store inst index segment)
    (bindings : InitializerBindings store inst) :
    runtime.store.instantiate.Store.check_element_bounds memory hooks floats allocator store platform instIndex index
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧ ErrorAllowed (PrecheckResourceCause allocator view store inst) out.1 ⦄ := by
  cases mode : segment.mode with
  | Active tableIndex offset =>
    simp only [ElementPrecheckReady, mode] at ready
    obtain ⟨function, code, words, addr, table, mapping, hc, compiled, resolved, ht, htable⟩ := ready
    apply WP.spec_mono (element_bounds_active_resource_causes memory hooks floats allocator law store platform instIndex index inst segment
      tableIndex offset function code words addr table hi helem mode mapping hc compiled resolved bindings ht htable)
    rintro ⟨result, after, host⟩ ⟨sameStore, sameHost, errors⟩
    refine ⟨sameStore, sameHost, ?_⟩
    cases result with
    | Ok value => trivial
    | Err error =>
      rcases errors error rfl with resource | ⟨rfl, outside⟩
      · exact Or.inl ⟨index,tableIndex,offset,function,code,Or.inl ⟨segment,helem,mode,mapping⟩,hc,compiled,resource⟩
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

theorem data_bounds_ready_resource_causes (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (memoryLaws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.ModuleInst) (segment : Itasca.module.Data)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hdata : inst.module.module.tail.data.val[index.val]? = some segment)
    (ready : DataPrecheckReady store inst index segment)
    (bindings : InitializerBindings store inst) :
    runtime.store.instantiate.Store.check_data_bounds memory hooks floats allocator store platform instIndex index
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧ ErrorAllowed (PrecheckResourceCause allocator view store inst) out.1 ⦄ := by
  cases mode : segment.mode with
  | Active memoryIndex offset =>
    simp only [DataPrecheckReady, mode] at ready
    obtain ⟨function, code, words, addr, mem, mapping, hc, compiled, resolved, hm, hmemory⟩ := ready
    apply WP.spec_mono (data_bounds_active_resource_causes memory hooks floats allocator law view memoryLaws store platform instIndex index
      inst segment memoryIndex offset function code words addr mem hi hdata mode mapping hc compiled resolved bindings hm hmemory)
    rintro ⟨result, after, host⟩ ⟨sameStore, sameHost, errors⟩
    refine ⟨sameStore, sameHost, ?_⟩
    cases result with
    | Ok value => trivial
    | Err error =>
      rcases errors error rfl with resource | ⟨rfl, outside⟩
      · exact Or.inl ⟨index,memoryIndex,offset,function,code,Or.inr ⟨segment,hdata,mode,mapping⟩,hc,compiled,resource⟩
      · exact Or.inr (Or.inr ⟨rfl, index, segment, memoryIndex, offset, words, addr, mem,
          hdata, mode, resolved, hm, hmemory, outside⟩)
  | Passive =>
    apply WP.spec_mono (data_bounds_inactive memory hooks floats allocator store platform instIndex index
      inst segment hi hdata mode)
    rintro out rfl
    exact ⟨rfl, rfl, trivial⟩

theorem element_precheck_loop_resource_causes (law : Platform.AllocCorrect allocator) (view : M → Slice U8)
    (store : runtime.store.Store M) (platform : P) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (allowed : ErrorAllowed (PrecheckResourceCause allocator view store inst) status)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (bindings : InitializerBindings store inst)
    (certificates : ∀ index : Usize, index.val < inst.module.module.env.elements.length →
      ∃ segment, inst.module.module.env.elements.val[index.val]? = some segment ∧
        ElementPrecheckReady store inst index segment)
    (hstart : start.val ≤ inst.module.module.env.elements.length) :
    runtime.store.instantiate.Store.prepare_instance_loop10 memory hooks floats allocator store platform status start instIndex
      ⦃ out => ∃ finalStatus, out = storeParts store platform finalStatus ∧ ErrorAllowed (PrecheckResourceCause allocator view store inst) finalStatus ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop10
  apply loop.spec_decr_nat (fun state => inst.module.module.env.elements.length - state.2.2.2.val)
    (fun state => state.1 = store ∧ state.2.1 = platform ∧
      state.2.2.2.val ≤ inst.module.module.env.elements.length ∧
      ErrorAllowed (PrecheckResourceCause allocator view store inst) state.2.2.1)
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
        step with element_bounds_ready_resource_causes memory hooks floats allocator law view store platform instIndex index
          inst segment hi helem ready bindings as ⟨result, after, host', hs, hp, errors⟩
        subst after host'
        cases result <;> step as ⟨next, hnext⟩ <;> exact ⟨by omega, errors, by omega⟩
    · simp only [WP.spec_ok]
      exact ⟨_, rfl, hallowed⟩
  · exact ⟨rfl, rfl, hstart, allowed⟩

theorem data_precheck_loop_resource_causes (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (memoryLaws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (platform : P) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (allowed : ErrorAllowed (PrecheckResourceCause allocator view store inst) status)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (bindings : InitializerBindings store inst)
    (certificates : ∀ index : Usize, index.val < inst.module.module.tail.data.length →
      ∃ segment, inst.module.module.tail.data.val[index.val]? = some segment ∧
        DataPrecheckReady store inst index segment)
    (hstart : start.val ≤ inst.module.module.tail.data.length) :
    runtime.store.instantiate.Store.prepare_instance_loop11 memory hooks floats allocator store platform status start instIndex
      ⦃ out => ∃ finalStatus, out = storeParts store platform finalStatus ∧ ErrorAllowed (PrecheckResourceCause allocator view store inst) finalStatus ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop11
  apply loop.spec_decr_nat (fun state => inst.module.module.tail.data.length - state.2.2.2.val)
    (fun state => state.1 = store ∧ state.2.1 = platform ∧
      state.2.2.2.val ≤ inst.module.module.tail.data.length ∧
      ErrorAllowed (PrecheckResourceCause allocator view store inst) state.2.2.1)
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
        step with data_bounds_ready_resource_causes memory hooks floats allocator law view memoryLaws store platform instIndex index
          inst segment hi helem ready bindings as ⟨result, after, host', hs, hp, errors⟩
        subst after host'
        cases result <;> step as ⟨next, hnext⟩ <;> exact ⟨by omega, errors, by omega⟩
    · simp only [WP.spec_ok]
      exact ⟨_, rfl, hallowed⟩
  · exact ⟨rfl, rfl, hstart, allowed⟩

end Itasca.Runtime.Store

end
