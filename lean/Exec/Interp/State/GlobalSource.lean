import Exec.Representation.Collection
import Exec.Interp.State.Globals
import Exec.Spec.Globals

namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt
open Exec.Store

/-- The two-word concrete replacement decodes to the generated global update.
The same identity covers scalar writes by retaining the original high word. -/
theorem global_write_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.Instance) (ambient : frame)
    (index : U32) (address : runtime.GlobalAddr) (old : runtime.store.GlobalInstance)
    (low high : U64) (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (found : store.globals.val[address.index.val]? = some old) :
    decodeStore view code {store with globals := store.globals.set address.index {old with lo := low, hi := high}} =
      Spec.globalWrite (decodeStore view code store) ambient index.val (decodeWords old.ty.valtype low high) := by
  have read : ambient.MODULE.GLOBALS[index.val]! = address.index.val := by
    rw [moduleEq]
    simp only [decodeInstance, List.getElem!_eq_getElem?_getD, List.getElem?_map, mapped, Option.map_some, Option.getD_some]
  have lists := Exec.Representation.map_set_modify decodeGlobal
    (fun global => {global with VALUE := decodeWords old.ty.valtype low high})
    store.globals.val address.index.val old {old with lo := low, hi := high} found rfl
  unfold Spec.globalWrite
  rw [read]
  unfold decodeStore
  simp only [alloc.vec.Vec.set_val_eq, lists]
  rfl

/-- Global lookup follows the generated source rule for every value type,
including references and vectors. -/
theorem global_read_source {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.Instance) (ambient : frame)
    (index : U32) (address : runtime.GlobalAddr) (value : runtime.store.GlobalInstance)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (found : store.globals.val[address.index.val]? = some value)
    (storeWf : wf_store (decodeStore view code store)) (ambientWf : wf_frame ambient) :
    StepH ⟨⟨decodeStore view code store,ambient⟩,[.GLOBAL_GET (.mk_uN index.val)]⟩ []
      ⟨⟨decodeStore view code store,ambient⟩,vals [decodeWords value.ty.valtype value.lo value.hi]⟩ := by
  apply Spec.global_get_step _ _ _ address.index.val (decodeGlobal value) storeWf ambientWf (by scalar_tac)
  · rw [moduleEq]
    simp [decodeInstance, mapped]
  · simp [decodeStore, found]

/-- Concrete global replacement performs the source GLOBAL_SET transition.
Input value well-formedness is a structural obligation of the active stack. -/
theorem global_write_source {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.Instance) (ambient : frame)
    (index : U32) (address : runtime.GlobalAddr) (old : runtime.store.GlobalInstance)
    (low high : U64) (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (found : store.globals.val[address.index.val]? = some old)
    (storeWf : wf_store (decodeStore view code store)) (ambientWf : wf_frame ambient)
    (valueWf : wf_val (decodeWords old.ty.valtype low high)) :
    StepH ⟨⟨decodeStore view code store,ambient⟩,
      [admininstr_val (decodeWords old.ty.valtype low high),.GLOBAL_SET (.mk_uN index.val)]⟩ []
      ⟨⟨decodeStore view code {store with globals := store.globals.set address.index {old with lo := low, hi := high}},ambient⟩,[]⟩ := by
  rw [global_write_decodes view code store inst ambient index address old low high moduleEq mapped found]
  apply Spec.global_set_step _ _ _ _ storeWf ambientWf (by scalar_tac) valueWf
  rw [moduleEq]
  simp only [decodeInstance, List.length_map]
  exact (List.getElem?_eq_some_iff.mp mapped).1
end Exec.Interp
