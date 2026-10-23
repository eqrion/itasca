import Exec.Representation.Collection
import Exec.Store.Initialization.Initializer
import Exec.Interp.Relations.Range

/-! Wasm1 active-segment prechecks evaluate certified constant offsets and check
bounds without modifying a retained object. -/
namespace Exec.Store
open Aeneas Aeneas.Std

private theorem value_i32_eq (value : runtime.Value) (typed : Interp.rawType value = .I32) :
    ∃ bits, runtime.Value.i32 value = .ok (.Ok bits) := by
  cases value <;> simp_all [Interp.rawType, runtime.Value.i32]

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem element_bounds_inactive (store : runtime.store.Store M) (platform : P)
    (instIndex index : Usize) (inst : runtime.store.ModuleInst) (segment : Itasca.module.Element)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (helem : inst.module.module.env.elements.val[index.val]? = some segment)
    (inactive : segment.mode = .Passive ∨ segment.mode = .Declarative) :
    runtime.store.instantiate.Store.check_element_bounds memory hooks floats allocator store platform instIndex index
      ⦃ out => out = (.Ok (), store, platform) ⦄ := by
  unfold runtime.store.instantiate.Store.check_element_bounds
  step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [runtime.compiler.ExecutableModule.env, module.Module.env,
    Itasca.module.Module.impl.env, module.Env.elements, Itasca.module.Env.impl.elements, bind_ok]
  step with Exec.Representation.slice_index_given inst.module.module.env.elements.deref index segment
    (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
  subst found
  rcases inactive with inactive | inactive <;> simp [inactive]

theorem element_bounds_active (law : Platform.AllocCorrect allocator)
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
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ⦄ := by
  unfold runtime.store.instantiate.Store.check_element_bounds
  step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [runtime.compiler.ExecutableModule.env, module.Module.env,
    Itasca.module.Module.impl.env, module.Env.elements, Itasca.module.Env.impl.elements, bind_ok]
  step with Exec.Representation.slice_index_given inst.module.module.env.elements.deref index segment
    (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
  subst found
  rw [active]
  step with Interp.vec_index_given inst.module.element_offsets index (some function) mapping
    as ⟨found, hfound⟩
  subst found
  step with eval_const_owned memory hooks floats allocator law store platform instIndex function
    inst code offset .I32 words hi hc compiled resolved bindings
    as ⟨result, after, host, hs, hp, hvalue⟩
  subst after host
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok value =>
    obtain ⟨bits, hbits⟩ := value_i32_eq value (hvalue value rfl).2
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hbits]
    step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
    subst found
    step with Exec.Representation.slice_index_given inst.module.module.env.elements.deref index segment
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
    cases checked <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem data_bounds_inactive (store : runtime.store.Store M) (platform : P)
    (instIndex index : Usize) (inst : runtime.store.ModuleInst) (segment : Itasca.module.Data)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hdata : inst.module.module.tail.data.val[index.val]? = some segment)
    (inactive : segment.mode = .Passive) :
    runtime.store.instantiate.Store.check_data_bounds memory hooks floats allocator store platform instIndex index
      ⦃ out => out = (.Ok (), store, platform) ⦄ := by
  unfold runtime.store.instantiate.Store.check_data_bounds
  step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [runtime.compiler.ExecutableModule.tail, module.Module.tail,
    Itasca.module.Module.impl.tail, bind_ok]
  step with Interp.vec_index_given inst.module.module.tail.data index segment hdata as ⟨found, hfound⟩
  subst found
  simp [inactive]

theorem data_bounds_active (law : Platform.AllocCorrect allocator)
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
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ⦄ := by
  unfold runtime.store.instantiate.Store.check_data_bounds
  step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [runtime.compiler.ExecutableModule.tail, module.Module.tail,
    Itasca.module.Module.impl.tail, bind_ok]
  step with Interp.vec_index_given inst.module.module.tail.data index segment helem as ⟨found, hfound⟩
  subst found
  rw [active]
  step with Interp.vec_index_given inst.module.data_offsets index (some function) mapping
    as ⟨found, hfound⟩
  subst found
  step with eval_const_owned memory hooks floats allocator law store platform instIndex function
    inst code offset .I32 words hi hc compiled resolved bindings
    as ⟨result, after, host, hs, hp, hvalue⟩
  subst after host
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok value =>
    obtain ⟨bits, hbits⟩ := value_i32_eq value (hvalue value rfl).2
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
    cases checked <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Exec.Store
