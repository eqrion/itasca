import Itasca.Runtime.Store.Preparation.AllocationErrors
import Itasca.Runtime.Store.Api.DefineTable
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

private theorem limits_success (limits : Itasca.types.Limits) (maximum : U32)
    (fit : LimitsFit limits maximum) : runtime.store.check_limits limits maximum = .ok (.Ok ()) := by
  obtain ⟨answer, called, result⟩ := WP.spec_imp_exists (check_limits_spec limits maximum)
  simpa [fit, result] using called

theorem define_table_errors {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (ty : Itasca.types.TableType)
    (fit : LimitsFit ty.limits core.num.U32.MAX)
    (out : core.result.Result runtime.TableAddr runtime.ExecError × runtime.store.Store M)
    (run : runtime.store.Store.define_table_with memory allocator store ty = .ok out) :
    ErrorAllowed ResourceError out.1 := by
  unfold runtime.store.Store.define_table_with at run
  simp only [limits_success ty.limits core.num.U32.MAX fit] at run
  repeat' allocation_error_step run using allocator, law

theorem define_global_errors {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (ty : Itasca.types.GlobalType) (value : runtime.Value)
    (typed : ty.valtype = Interp.rawType value) (owned : Interp.ValueOwnedFits store.id value)
    (out : core.result.Result runtime.GlobalAddr runtime.ExecError × runtime.store.Store M)
    (run : runtime.store.Store.define_global_with memory allocator store ty value = .ok out) :
    ErrorAllowed ResourceError out.1 := by
  unfold runtime.store.Store.define_global_with at run
  simp only [check_value_owned memory store value owned, value_type_exact, typed,
    core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
    value_type_eq_self, bind_ok, lift, Bool.not_true] at run
  repeat' allocation_error_step run using allocator, law

theorem define_memory_errors {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (ty : Itasca.types.MemType) (buffer : M)
    (fit : LimitsFit ty.limits 65536#u32)
    (length : (view buffer).length = ty.limits.min.val * 65536)
    (out : core.result.Result runtime.MemoryAddr runtime.ExecError × runtime.store.Store M)
    (run : runtime.store.Store.define_memory_with memory allocator store ty buffer = .ok out) :
    ErrorAllowed ResourceError out.1 := by
  have multiply : (UScalar.cast .U64 ty.limits.min) * 65536#u64
      ⦃ size => size.val = ty.limits.min.val * 65536 ⦄ := by
    step as ⟨size, sizeValue⟩
    scalar_tac
  obtain ⟨size, called, sizeValue⟩ := WP.spec_imp_exists multiply
  have sameSize : UScalar.cast .U64 (view buffer).len = size := by scalar_tac
  unfold runtime.store.Store.define_memory_with at run
  simp only [limits_success ty.limits 65536#u32 fit, lift, called,
    laws.read buffer, bind_ok, sameSize, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at run
  repeat' allocation_error_step run using allocator, law

end Itasca.Runtime.Store
