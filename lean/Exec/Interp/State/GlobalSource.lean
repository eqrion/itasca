import Exec.Representation.Collection
import Exec.Interp.State.Globals
import Exec.Spec.Globals

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt
open Itasca.Runtime.Store

/-- The two-word concrete replacement decodes to the generated global update.
The same identity covers scalar writes by retaining the original high word. -/
theorem global_write_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (index : U32) (address : runtime.GlobalAddr) (old : runtime.store.GlobalInst)
    (low high : U64) (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (found : store.globals.val[address.index.val]? = some old) :
    decodeStore view code {store with globals := store.globals.set address.index {old with lo := low, hi := high}} =
      Spec.globalWrite (decodeStore view code store) ambient index.val (decodeWords old.ty.valtype low high) := by
  have read : ambient.MODULE.GLOBALS[index.val]! = address.index.val := by
    rw [moduleEq]
    simp only [decodeInstance, List.getElem!_eq_getElem?_getD, List.getElem?_map, mapped, Option.map_some, Option.getD_some]
  have lists := Itasca.Runtime.Representation.map_set_modify decodeGlobal
    (fun global => {global with VALUE := decodeWords old.ty.valtype low high})
    store.globals.val address.index.val old {old with lo := low, hi := high} found rfl
  unfold Spec.globalWrite
  rw [read]
  unfold decodeStore
  simp only [alloc.vec.Vec.set_val_eq, lists]
  rfl

end Itasca.Runtime.Interp
