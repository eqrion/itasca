import Exec.Store.Invariant.DefinitionErrors
import Exec.Code.Local.Initializer.InitializerMappings
namespace Exec.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

theorem add_table_errors_metadata {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (ty : Itasca.types.TableType)
    (found : inst.module.module.env.table_types.val[index.val]? = some ty)
    (fit : LimitsFit ty.limits core.num.U32.MAX)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M × runtime.store.ModuleInst)
    (run : runtime.store.instantiate.Store.add_instance_table memory allocator store inst index = .ok out) :
    ErrorAllowed ResourceError out.1 ∧ out.2.2.module = inst.module := by
  unfold runtime.store.instantiate.Store.add_instance_table at run
  simp only [runtime.compiler.ExecutableModule.env, module.Module.env, Itasca.module.Module.impl.env,
    module.Env.table_types, Itasca.module.Env.impl.table_types, bind_ok] at run
  rw [Code.initializer_slice_index inst.module.module.env.table_types.deref index ty (by simpa [alloc.vec.Vec.deref] using found)] at run
  simp only [bind_ok] at run
  obtain ⟨⟨status, after⟩, defined, rest⟩ := normal_bind_exists _ _ _ run
  have cause := define_table_errors memory allocator law store ty fit _ defined
  clear run
  rename' rest => run
  repeat' allocation_error_step run using allocator, law

theorem add_memory_errors_metadata {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (ty : Itasca.types.MemType)
    (found : inst.module.module.env.mem_types.val[index.val]? = some ty)
    (fit : LimitsFit ty.limits 65536#u32)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M × runtime.store.ModuleInst)
    (run : runtime.store.instantiate.Store.add_instance_memory memory allocator store inst index = .ok out) :
    ErrorAllowed ResourceError out.1 ∧ out.2.2.module = inst.module := by
  have multiply : (UScalar.cast .U64 ty.limits.min) * 65536#u64
      ⦃ size => size.val = ty.limits.min.val * 65536 ⦄ := by
    step as ⟨size, sizeValue⟩
    scalar_tac
  obtain ⟨size, sizeRun, sizeValue⟩ := WP.spec_imp_exists multiply
  unfold runtime.store.instantiate.Store.add_instance_memory at run
  simp only [runtime.compiler.ExecutableModule.env, module.Module.env, Itasca.module.Module.impl.env,
    module.Env.mem_types, Itasca.module.Env.impl.mem_types, bind_ok] at run
  rw [Code.initializer_slice_index inst.module.module.env.mem_types.deref index ty (by simpa [alloc.vec.Vec.deref] using found)] at run
  simp only [bind_ok,
    lift, sizeRun] at run
  split at run
  · repeat' allocation_error_step run using allocator, law
  · rename_i fits
    have bounded : size.val ≤ Usize.max := by scalar_tac
    have castExact := cast_usize_exact size bounded
    obtain ⟨buffer, createRun, zeroes⟩ := WP.spec_imp_exists (laws.create (UScalar.cast .Usize size))
    simp only [createRun] at run
    cases buffer with
    | none => repeat' allocation_error_step run using allocator, law
    | some buffer =>
      have length : (view buffer).length = ty.limits.min.val * 65536 := by
        have contents := zeroes buffer rfl
        have lengths := congrArg List.length contents
        simpa [castExact, sizeValue] using lengths
      simp only [bind_ok] at run
      obtain ⟨within, withinRun, rest⟩ := normal_bind_exists _ _ _ run
      clear run
      rename' rest => run
      split at run
      · obtain ⟨⟨status, after⟩, defined, rest⟩ := normal_bind_exists _ _ _ run
        have cause := define_memory_errors memory allocator law view laws store ty buffer fit length _ defined
        clear run
        rename' rest => run
        repeat' allocation_error_step run using allocator, law
      · repeat' allocation_error_step run using allocator, law

end Exec.Store
