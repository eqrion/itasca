import Exec.Store.Initialization.InitializerSource
import Exec.Store.Initialization.InitializerResolve
import Exec.Store.Invariant.ValueDecode
namespace Exec.Store
open Aeneas Aeneas.Std Itasca

/-- The source initial frame reads the same imported globals and function
addresses as the staged runtime instance. Defined globals are not in the
constant-expression typing context. -/
structure InitializerSourceContext {M : Type} (sourceStore : _root_.store)
    (sourceInstance : moduleinst) (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) : Prop where
  functions : sourceInstance.FUNCS = inst.funcs.val.map (fun address => address.index.val)
  globals : ∀ (index : U32) address global,
    index.val < inst.module.module.env.global_types.val.length →
    index.val < inst.module.module.env.num_imported_globals.val →
    inst.globals.val[index.val]? = some address →
    store.globals.val[address.index.val]? = some global →
    fun_global ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (.mk_uN index.val) = decodeGlobal global

theorem InitializerSourceContext.expression {M : Type} {sourceStore sourceInstance}
    {store : runtime.store.Store M} {inst expr ty words}
    (context : InitializerSourceContext sourceStore sourceInstance store inst)
    (valid : ModuleConstants.Valid inst.module.module.env expr ty)
    (resolved : Interp.InitializerResolution store inst expr ty words)
    (storeWf : wf_store sourceStore) (frameWf : wf_frame ⟨[], sourceInstance⟩) :
    Eval_expr ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (ModuleConstants.expression expr)
      ⟨sourceStore, ⟨[], sourceInstance⟩⟩
      [decodeWords ty ((words[0]?).getD 0#u64) ((words[1]?).getD 0#u64)] := by
  apply initializer_resolution_source_in_state store inst expr ty words resolved
    sourceStore sourceInstance context.functions ?_ storeWf frameWf
  intro index address global equal mapped found
  subst expr
  cases valid with
  | globalGet _ _ typedBound _ imported _ => exact context.globals index address global typedBound imported mapped found

/-- Earlier source lookups are unchanged when only defined globals append. -/
theorem InitializerSourceContext.extend {M : Type} {sourceStore sourceInstance}
    {before after : runtime.store.Store M} {old next : runtime.store.ModuleInst}
    (context : InitializerSourceContext sourceStore sourceInstance before old)
    (imports : InitializerImports before old)
    (source : next.module = old.module) (functions : next.funcs = old.funcs)
    (globalMap : next.globals.val.take old.globals.length = old.globals.val)
    (globals : after.globals.val.take before.globals.length = before.globals.val) :
    InitializerSourceContext sourceStore sourceInstance after next := by
  refine ⟨by simpa [functions] using context.functions, ?_⟩
  intro index address global typedBound imported mapped found
  rw [source] at typedBound imported
  obtain ⟨oldAddress, oldGlobal, oldMapped, oldFound, _⟩ := imports.globals index
    old.module.module.env.global_types.val[index.val] (List.getElem?_eq_getElem typedBound) imported
  have mapBound := (List.getElem?_eq_some_iff.mp oldMapped).1
  have mapRetained := oldMapped
  rw [← globalMap, List.getElem?_take, if_pos mapBound] at mapRetained
  have sameAddress : oldAddress = address := Option.some.inj (mapRetained.symm.trans mapped)
  subst oldAddress
  have globalBound := (List.getElem?_eq_some_iff.mp oldFound).1
  have globalRetained := oldFound
  rw [← globals, List.getElem?_take, if_pos globalBound] at globalRetained
  have sameGlobal : oldGlobal = global := Option.some.inj (globalRetained.symm.trans found)
  subst oldGlobal
  exact context.globals index address global typedBound imported oldMapped oldFound

/-- Preparation has not changed global contents; its imported address map is
exactly the initial source frame's global namespace. -/
theorem InitializerSourceContext.of_maps {M : Type} (view : M → Slice U8)
    (code : CodeInterpretation) (before store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (sourceInstance : moduleinst)
    (functions : sourceInstance.FUNCS = inst.funcs.val.map (fun address => address.index.val))
    (addresses : sourceInstance.GLOBALS = inst.globals.val.map (fun address => address.index.val))
    (globals : store.globals = before.globals) :
    InitializerSourceContext (decodeStore view code before) sourceInstance store inst := by
  refine ⟨functions, ?_⟩
  intro index address global _ _ mapped found
  rw [globals] at found
  simp [fun_global, decodeStore, addresses, proj_uN_0,
    List.getElem!_eq_getElem?_getD, List.getElem?_map, mapped, found]
end Exec.Store
