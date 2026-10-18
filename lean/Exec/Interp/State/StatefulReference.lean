import Exec.Interp.Relations.ReferenceConstructors
import Exec.Abs.Stateful.Transition
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt Exec.Store

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem stateful_ref_null_effect (exec : runtime.interp.Execution) (base : Usize) (dst : U32)
    (type : Itasca.types.ElemType) (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (slotBound : base.val+dst.val < exec.slots.length) :
    runtime.interp.admin_ref_null memory hooks floats allocator exec base dst ⦃ out =>
      out.1 = .Ok () ∧ SlotsEffect exec out.2 (exec.slots.val.set (base.val+dst.val) 0#u64) ∧
      Abs.Stateful.Transition state f rest after (.refNull (decodeElemType type))
        (Abs.advance state {f with code := after,vals := f.vals++[.REF_NULL (decodeElemType type)]} rest) ⦄ := by
  apply WP.spec_mono (ref_null_effect memory hooks floats allocator exec base dst slotBound)
  intro out effect
  exact ⟨effect.1,effect.2,{},trivial,rfl⟩

theorem stateful_ref_func_effect (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst func : U32) (inst : runtime.store.Instance) (address : runtime.FuncAddr)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.funcs.val[func.val]? = some address) (issued : address.index.val < store.funcs.length)
    (slotBound : base.val+dst.val < exec.slots.length)
    (moduleEq : f.module = decodeInstance store inst) :
    runtime.interp.admin_ref_func memory hooks floats allocator exec store instanceIndex base dst func ⦃ out =>
      out.1 = .Ok () ∧ out.2.2 = store ∧ ∃ word : U64,
        word.val = address.index.val+1 ∧
        SlotsEffect exec out.2.1 (exec.slots.val.set (base.val+dst.val) word) ∧
        Abs.Stateful.Transition state f rest after (.refFunc func.val)
          (Abs.advance state {f with code := after,vals := f.vals++[.REF_FUNC_ADDR address.index.val]} rest) ⦄ := by
  have addressBound : address.index.val < U64.max := by
    have bound := store.funcs.property
    rcases Usize.bounds_eq with h | h <;> scalar_tac
  apply WP.spec_mono (ref_func_effect memory hooks floats allocator exec store instanceIndex base dst func inst address found mapped addressBound slotBound)
  intro out effect
  obtain ⟨success,same,word,wordEq,slots⟩ := effect
  refine ⟨success,same,word,wordEq,slots,{},trivial,?_⟩
  simp [Abs.Stateful.evaluate,Abs.Stateful.refFunc,moduleEq,decodeInstance,List.getElem?_map,mapped]

theorem stateful_ref_is_null_effect (exec : runtime.interp.Execution) (base : Usize) (dst src : U32)
    (type : Itasca.types.ElemType) (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (front : List val)
    (values : f.vals = front++[val_ref (decodeRef type exec.slots.val[base.val+src.val]!)])
    (sourceBound : base.val+src.val < exec.slots.length) (destinationBound : base.val+dst.val < exec.slots.length) :
    runtime.interp.admin_ref_is_null memory hooks floats allocator exec base dst src ⦃ out =>
      out.1 = .Ok () ∧ ∃ word : U64,
        word.val = Spec.referenceIsNull (decodeRef type exec.slots.val[base.val+src.val]!) ∧
        SlotsEffect exec out.2 (exec.slots.val.set (base.val+dst.val) word) ∧
        Abs.Stateful.Transition state f rest after .refIsNull
          (Abs.advance state {f with code := after,vals := front++[Abs.integerVal .I32 word.val]} rest) ⦄ := by
  apply WP.spec_mono (ref_is_null_effect memory hooks floats allocator exec base dst src sourceBound destinationBound)
  intro out effect
  let word : U64 := if exec.slots.val[base.val+src.val]! = 0#u64 then 1#u64 else 0#u64
  have wordEq : word.val = Spec.referenceIsNull (decodeRef type exec.slots.val[base.val+src.val]!) := by
    rw [decode_ref_is_null]
    dsimp only [word]
    split <;> rfl
  refine ⟨effect.1,word,wordEq,effect.2,{},trivial,?_⟩
  simp only [Abs.Stateful.evaluate,Abs.Stateful.refIsNull,values,Abs.pop_append,Abs.Stateful.asReference_value,wordEq]
end Exec.Interp
