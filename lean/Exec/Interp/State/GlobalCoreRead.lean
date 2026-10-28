import Exec.Interp.Relations.WordEncoding
import Exec.Interp.Relations.PrefixEffect
import Exec.Interp.State.GlobalSource
import Exec.Abs.Core.Globals

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt

theorem core_global_get_value {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (s : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (index : U32)
    (storeEq : s.store = Store.decodeStore view code store)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object) :
    Abs.Core.globalGet s f rest index.val after =
      .next {s with frames := {f with code := after, vals := f.vals ++ [Store.decodeWords object.ty.valtype object.lo object.hi]} :: rest} := by
  simp only [Abs.Core.globalGet,moduleEq,Store.decodeInstance,List.getElem?_map,mapped,Option.map_some,
    storeEq,Store.decodeStore,issued,Store.decodeGlobal,Abs.advance]

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem global_get_core (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (dst index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (s : Abs.AState) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (storeEq : s.store = Store.decodeStore view code store)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (position : dst.val = Code.slots ((f.locals ++ f.vals).map Code.valueType))
    (capacity : raw.base.val + dst.val < exec.slots.length)
    (scalar : object.ty.valtype ≠ .V128)
    (small : object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32) :
    runtime.interp.execute_global_get memory exec store raw.instance raw.base dst index ⦃ out =>
      out.1 = .Ok () ∧ out.2.2 = store ∧
      ∃ nextFrame, Abs.Core.globalGet s f rest index.val after = .next {s with frames := nextFrame :: rest} ∧
        FrameSlots out.2.1 raw nextFrame ∧ {out.2.1 with slots := exec.slots} = exec ∧ SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ⦄ := by
  have abstract := core_global_get_value view code store inst address object s f rest after index storeEq moduleEq mapped issued
  have represented := ValuesAt.append_scalar slots object.ty.valtype object.lo object.hi scalar small
    (by simpa only [position] using capacity)
  apply WP.spec_mono (global_get_dispatch_effect memory exec store raw.instance raw.base dst index
    inst address object found mapped issued capacity)
  intro out effect
  refine ⟨effect.1,effect.2.2,_,abstract,?_,effect.2.1.2,?_⟩
  · change ValuesAt out.2.1.slots.val raw.base.val (f.locals ++ (f.vals ++ [_]))
    rw [effect.2.1.1,position]
    simpa only [List.append_assoc] using represented
  · rw [effect.2.1.1]
    exact SlotPrefix.set _ _ _ _ (by omega)

theorem global_get2_core (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (dst index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (s : Abs.AState) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (storeEq : s.store = Store.decodeStore view code store)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (position : dst.val = Code.slots ((f.locals ++ f.vals).map Code.valueType))
    (capacity : raw.base.val + dst.val + 2 ≤ exec.slots.length)
    (vector : object.ty.valtype = .V128) :
    runtime.interp.execute_global_get2 memory exec store raw.instance raw.base dst index ⦃ out =>
      out.1 = .Ok () ∧ out.2.2 = store ∧
      ∃ nextFrame, Abs.Core.globalGet s f rest index.val after = .next {s with frames := nextFrame :: rest} ∧
        FrameSlots out.2.1 raw nextFrame ∧ {out.2.1 with slots := exec.slots} = exec ∧ SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ⦄ := by
  have abstract := core_global_get_value view code store inst address object s f rest after index storeEq moduleEq mapped issued
  have represented := ValuesAt.append_vector slots object.lo object.hi (by simpa only [position] using capacity)
  apply WP.spec_mono (global_get2_dispatch_effect memory exec store raw.instance raw.base dst index
    inst address object found mapped issued capacity)
  intro out effect
  refine ⟨effect.1,effect.2.2,_,abstract,?_,effect.2.1.2,?_⟩
  · change ValuesAt out.2.1.slots.val raw.base.val (f.locals ++ (f.vals ++ [_]))
    rw [effect.2.1.1,position,vector]
    simpa only [List.append_assoc] using represented
  · rw [effect.2.1.1]
    exact (SlotPrefix.set _ _ _ _ (by omega)).trans (SlotPrefix.set _ _ _ _ (by omega))

end Itasca.Runtime.Interp
