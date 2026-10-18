import Exec.Interp.Relations.InitializerAdmin
import Exec.Interp.Simd.Common.SimdValueSlots
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem dispatch_const_v128_values {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index instIndex function base : Usize) (dst pool : U32)
    (inst : runtime.store.Instance) (code : runtime.bytecode.CompiledFunction) (value : U128)
    (front : List val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : inst.module.functions.val[function.val]? = some code)
    (metadata : code.v128_pool.val[pool.val]? = some value)
    (position : dst.val = Code.slots (front.map Code.valueType))
    (represented : ValuesAt exec.slots.val base.val front)
    (capacity : base.val + dst.val + 2 ≤ exec.slots.length) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index instIndex function base (.ConstV128 dst pool)
      ⦃ out => out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
        SlotsEffect exec out.2.1 (simdResultSlots exec.slots.val (base.val+dst.val) 2#u32 value) ∧
        ValuesAt out.2.1.slots.val base.val (front ++ [.VCONST .V128 (.mk_uN value.val)]) ⦄ := by
  simp only [runtime.interp.dispatch]
  step with const_v128_effect memory hooks floats allocator exec store instIndex function base dst pool inst code value
    found compiled metadata (by omega) as ⟨result,execution,storeNext,ok,unchanged,slots⟩
  have exactSlots : SlotsEffect exec execution (simdResultSlots exec.slots.val (base.val+dst.val) 2#u32 value) := by
    with_unfolding_all exact slots
  refine ⟨ok,unchanged,exactSlots,?_⟩
  rw [exactSlots.1,position]
  exact represented.simd_vector_result value (by simpa only [position] using capacity)
end Exec.Interp
