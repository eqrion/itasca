import Exec.Interp.State.GlobalSource

namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt
open Exec.Store

private theorem decodeWords_scalar (ty : Itasca.types.ValueType) (lo hi : U64)
    (scalar : ty ≠ .V128) : decodeWords ty lo hi = decodeWords ty lo 0#u64 := by
  cases ty <;> simp_all [decodeWords]

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

/-- Scalar GLOBAL_GET dispatch returns the exact source global and modifies
only its destination word. -/
theorem global_get_dispatch_source (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst global : U32) (inst : runtime.store.Instance)
    (address : runtime.GlobalAddr) (value : runtime.store.GlobalInstance) (ambient : frame)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.globals.val[global.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some value)
    (capacity : base.val + dst.val < exec.slots.length)
    (scalar : value.ty.valtype ≠ .V128)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (storeWf : wf_store (decodeStore view code store)) (ambientWf : wf_frame ambient) :
    runtime.interp.admin_global_get memory hooks floats allocator exec store instanceIndex base dst global
      ⦃ out => out.1 = .Ok () ∧ SlotsEffect exec out.2.1
        (exec.slots.val.set (base.val + dst.val) value.lo) ∧ out.2.2 = store ∧
        StepH ⟨⟨decodeStore view code store,ambient⟩,[.GLOBAL_GET (.mk_uN global.val)]⟩ []
          ⟨⟨decodeStore view code out.2.2,ambient⟩,vals [decodeWords value.ty.valtype value.lo 0#u64]⟩ ⦄ := by
  have source := global_read_source view code store inst ambient global address value moduleEq mapped issued storeWf ambientWf
  rw [decodeWords_scalar _ _ _ scalar] at source
  apply WP.spec_mono (global_get_dispatch_effect memory hooks floats allocator exec store instanceIndex base
    dst global inst address value found mapped issued capacity)
  intro out effect
  exact ⟨effect.1,effect.2.1,effect.2.2,by simpa only [effect.2.2] using source⟩

/-- Two-word GLOBAL_GET dispatch also covers vector-valued globals. -/
theorem global_get2_dispatch_source (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst global : U32) (inst : runtime.store.Instance)
    (address : runtime.GlobalAddr) (value : runtime.store.GlobalInstance) (ambient : frame)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.globals.val[global.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some value)
    (capacity : base.val + dst.val + 2 ≤ exec.slots.length)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (storeWf : wf_store (decodeStore view code store)) (ambientWf : wf_frame ambient) :
    runtime.interp.admin_global_get2 memory hooks floats allocator exec store instanceIndex base dst global
      ⦃ out => out.1 = .Ok () ∧ SlotsEffect exec out.2.1
        ((exec.slots.val.set (base.val + dst.val) value.lo).set (base.val + dst.val + 1) value.hi) ∧ out.2.2 = store ∧
        StepH ⟨⟨decodeStore view code store,ambient⟩,[.GLOBAL_GET (.mk_uN global.val)]⟩ []
          ⟨⟨decodeStore view code out.2.2,ambient⟩,vals [decodeWords value.ty.valtype value.lo value.hi]⟩ ⦄ := by
  have source := global_read_source view code store inst ambient global address value moduleEq mapped issued storeWf ambientWf
  apply WP.spec_mono (global_get2_dispatch_effect memory hooks floats allocator exec store instanceIndex base
    dst global inst address value found mapped issued capacity)
  intro out effect
  exact ⟨effect.1,effect.2.1,effect.2.2,by simpa only [effect.2.2] using source⟩

/-- Scalar GLOBAL_SET dispatch implements the source write and preserves all
non-global metadata and the complete execution state. -/
theorem global_set_dispatch_source (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (src global : U32) (inst : runtime.store.Instance)
    (address : runtime.GlobalAddr) (value : runtime.store.GlobalInstance) (ambient : frame)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.globals.val[global.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some value)
    (capacity : base.val + src.val < exec.slots.length)
    (scalar : value.ty.valtype ≠ .V128)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (storeWf : wf_store (decodeStore view code store)) (ambientWf : wf_frame ambient)
    (inputWf : wf_val (decodeWords value.ty.valtype exec.slots.val[base.val + src.val]! 0#u64)) :
    runtime.interp.admin_global_set memory hooks floats allocator exec store instanceIndex base src global
      ⦃ out => out = (.Ok (),exec,{store with globals := store.globals.set address.index ({value with lo := exec.slots.val[base.val + src.val]!})}) ∧
        StepH ⟨⟨decodeStore view code store,ambient⟩,
          [admininstr_val (decodeWords value.ty.valtype exec.slots.val[base.val + src.val]! 0#u64),.GLOBAL_SET (.mk_uN global.val)]⟩ []
          ⟨⟨decodeStore view code out.2.2,ambient⟩,[]⟩ ⦄ := by
  have source := global_write_source view code store inst ambient global address value
    exec.slots.val[base.val + src.val]! value.hi moduleEq mapped issued storeWf ambientWf
    (by simpa only [decodeWords_scalar _ _ _ scalar] using inputWf)
  rw [decodeWords_scalar _ _ _ scalar] at source
  apply WP.spec_mono (global_set_dispatch_effect memory hooks floats allocator exec store instanceIndex base
    src global inst address value found mapped issued capacity)
  intro out effect
  exact ⟨effect,by simpa only [effect] using source⟩

/-- Two-word GLOBAL_SET dispatch retains the complete vector payload in the
source transition. -/
theorem global_set2_dispatch_source (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (src global : U32) (inst : runtime.store.Instance)
    (address : runtime.GlobalAddr) (value : runtime.store.GlobalInstance) (ambient : frame)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.globals.val[global.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some value)
    (capacity : base.val + src.val + 2 ≤ exec.slots.length)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (storeWf : wf_store (decodeStore view code store)) (ambientWf : wf_frame ambient)
    (inputWf : wf_val (decodeWords value.ty.valtype exec.slots.val[base.val + src.val]! exec.slots.val[base.val + src.val + 1]!)) :
    runtime.interp.admin_global_set2 memory hooks floats allocator exec store instanceIndex base src global
      ⦃ out => out = (.Ok (),exec,{store with globals := store.globals.set address.index ({value with lo := exec.slots.val[base.val + src.val]!, hi := exec.slots.val[base.val + src.val + 1]!})}) ∧
        StepH ⟨⟨decodeStore view code store,ambient⟩,
          [admininstr_val (decodeWords value.ty.valtype exec.slots.val[base.val + src.val]! exec.slots.val[base.val + src.val + 1]!),.GLOBAL_SET (.mk_uN global.val)]⟩ []
          ⟨⟨decodeStore view code out.2.2,ambient⟩,[]⟩ ⦄ := by
  have source := global_write_source view code store inst ambient global address value
    exec.slots.val[base.val + src.val]! exec.slots.val[base.val + src.val + 1]! moduleEq mapped issued storeWf ambientWf inputWf
  apply WP.spec_mono (global_set2_dispatch_effect memory hooks floats allocator exec store instanceIndex base
    src global inst address value found mapped issued capacity)
  intro out effect
  exact ⟨effect,by simpa only [effect] using source⟩
end Exec.Interp
