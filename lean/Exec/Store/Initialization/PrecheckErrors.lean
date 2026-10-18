import Exec.Representation.Collection
import Exec.Store.Initialization.PrecheckLoop
import Exec.Store.Initialization.InitializerErrors
import Exec.Store.Invariant.PrecommitError
namespace Exec.Store
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

theorem element_range_active_errors (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.Instance) (segment : Itasca.module.Element)
    (tableIndex : U32) (offset : Itasca.types.ConstExpr) (function : Usize)
    (code : runtime.bytecode.CompiledFunction) (words : List U64)
    (addr : runtime.TableAddr) (table : runtime.store.Table)
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
    runtime.store.instantiate.Store.element_range_for memory hooks floats allocator store platform instIndex index
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧
        ∀ error, out.1 = .Err error → ResourceError error ∨
          (error = .Trap .TableOutOfBounds ∧ table.elements.length < ((words[0]?).getD 0#u64).val % 2^32 + segment.init.length) ⦄ := by
  unfold runtime.store.instantiate.Store.element_range_for
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
  step with eval_const_exec_errors memory hooks floats allocator law store platform instIndex function
    inst code offset .I32 words hi hc compiled resolved (by simp)
    as ⟨result, after, host, hs, hp, hvalue, errors⟩
  subst after host
  cases result with
  | Err error =>
    obtain ⟨resource, rfl⟩ := errors error rfl
    simp [ResourceError,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok value =>
    obtain ⟨bits, hbits⟩ := value_i32_eq value (hvalue value rfl).1
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

theorem data_range_active_errors (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (memoryLaws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.Instance) (segment : Itasca.module.Data)
    (memoryIndex : U32) (offset : Itasca.types.ConstExpr) (function : Usize)
    (code : runtime.bytecode.CompiledFunction) (words : List U64)
    (addr : runtime.MemoryAddr) (mem : runtime.store.Memory M)
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
    runtime.store.instantiate.Store.data_range_for memory hooks floats allocator store platform instIndex index
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧
        ∀ error, out.1 = .Err error → ResourceError error ∨
          (error = .Trap .MemoryOutOfBounds ∧ (view mem.buf).length < ((words[0]?).getD 0#u64).val % 2^32 + segment.init.length) ⦄ := by
  unfold runtime.store.instantiate.Store.data_range_for
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
  step with eval_const_exec_errors memory hooks floats allocator law store platform instIndex function
    inst code offset .I32 words hi hc compiled resolved (by simp)
    as ⟨result, after, host, hs, hp, hvalue, errors⟩
  subst after host
  cases result with
  | Err error =>
    obtain ⟨resource, rfl⟩ := errors error rfl
    simp [ResourceError,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
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

end Exec.Store
