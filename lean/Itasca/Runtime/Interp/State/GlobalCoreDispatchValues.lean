import Itasca.Runtime.Interp.State.GlobalCoreDispatch
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem sourceType_width_two (ty : Itasca.types.ValueType) :
    Code.width (sourceType ty) = 2 ↔ ty = .V128 := by
  cases ty <;> simp [sourceType,Code.width]

theorem sourceType_width_scalar (ty : Itasca.types.ValueType) (scalar : ty ≠ .V128) :
    Code.width (sourceType ty) = 1 := by
  cases ty <;> simp_all [sourceType,Code.width]

theorem dispatch_global_get_core (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (dst index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (s : Abs.AState) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr) (platform : P) (frameIndex : Usize)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (storeEq : s.store = Store.decodeStore view code store)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (position : dst.val = Code.slots ((f.locals ++ f.vals).map Code.valueType))
    (capacity : raw.base.val + dst.val + Code.width (sourceType object.ty.valtype) ≤ exec.slots.length)
    (small : object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
      (Code.globalGetInstruction (decide (Code.width (sourceType object.ty.valtype) = 2)) dst index) ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.2 = platform ∧ out.2.2.1 = store ∧
      ∃ nextFrame, Abs.Core.globalGet s f rest index.val after = .next {s with frames := nextFrame :: rest} ∧
        FrameSlots out.2.1 raw nextFrame ∧ {out.2.1 with slots := exec.slots} = exec ∧ SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ⦄ := by
  classical
  have handler : (if decide (Code.width (sourceType object.ty.valtype) = 2) then
      runtime.interp.execute_global_get2 memory exec store raw.instance raw.base dst index
      else runtime.interp.execute_global_get memory exec store raw.instance raw.base dst index) ⦃ out => out.1 = .Ok () ∧ out.2.2 = store ∧ ∃ nextFrame, Abs.Core.globalGet s f rest index.val after = .next {s with frames := nextFrame :: rest} ∧ FrameSlots out.2.1 raw nextFrame ∧ {out.2.1 with slots := exec.slots} = exec ∧ SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ⦄ := by
    simp only [sourceType_width_two]
    by_cases vector : object.ty.valtype = .V128
    · simp only [vector,decide_true,ite_true]
      exact global_get2_core memory view code exec store raw dst index inst address object s f rest after
        found mapped issued storeEq moduleEq slots position (by simpa only [vector,sourceType,Code.width] using capacity) vector
    · simp only [vector,decide_false,ite_false]
      exact global_get_core memory view code exec store raw dst index inst address object s f rest after
        found mapped issued storeEq moduleEq slots position (by rw [sourceType_width_scalar _ vector] at capacity; omega) vector small
  apply WP.spec_mono (dispatch_globalGet memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
    (decide (Code.width (sourceType object.ty.valtype) = 2)) dst index handler)
  intro out effect
  exact ⟨effect.1.1,effect.2,effect.1.2⟩

theorem dispatch_global_set_core (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (src index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (s : Abs.AState) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr) (front : List val) (value : val)
    (platform : P) (frameIndex : Usize)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (storeEq : s.store = Store.decodeStore view code store)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f) (values : f.vals = front ++ [value])
    (position : src.val = Code.slots ((f.locals ++ front).map Code.valueType))
    (mutable : object.ty.mutability = .Var)
    (valueWf : wf_val value) (typed : sourceType object.ty.valtype = Code.valueType value) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
      (Code.globalSetInstruction (decide (Code.width (sourceType object.ty.valtype) = 2)) src index) ⦃ out =>
      out.2.2.2 = platform ∧ out.1 = .Ok () ∧ out.2.1 = exec ∧ FrameStoreMetadata store out.2.2.1 ∧
      ∃ nextFrame, Abs.Core.globalSet s f rest index.val after =
          .next {s with store := Store.decodeStore view code out.2.2.1, frames := nextFrame :: rest} ∧
        FrameSlots out.2.1 raw nextFrame ⦄ := by
  classical
  have handler : (if decide (Code.width (sourceType object.ty.valtype) = 2) then
      runtime.interp.execute_global_set2 memory exec store raw.instance raw.base src index
      else runtime.interp.execute_global_set memory exec store raw.instance raw.base src index) ⦃ out => out.1 = .Ok () ∧ out.2.1 = exec ∧ FrameStoreMetadata store out.2.2 ∧ ∃ nextFrame, Abs.Core.globalSet s f rest index.val after = .next {s with store := Store.decodeStore view code out.2.2, frames := nextFrame :: rest} ∧ FrameSlots out.2.1 raw nextFrame ⦄ := by
    simp only [sourceType_width_two]
    by_cases vector : object.ty.valtype = .V128
    · simp only [vector,decide_true,ite_true]
      exact global_set2_core memory view code exec store raw src index inst address object s f rest after front value
        found mapped issued storeEq moduleEq slots values position vector mutable valueWf typed
    · simp only [vector,decide_false,ite_false]
      exact global_set_core memory view code exec store raw src index inst address object s f rest after front value
        found mapped issued storeEq moduleEq slots values position vector mutable valueWf typed
  apply WP.spec_mono (dispatch_globalSet memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
    (decide (Code.width (sourceType object.ty.valtype) = 2)) src index handler)
  intro out effect
  exact ⟨effect.2,effect.1⟩

end Itasca.Runtime.Interp
