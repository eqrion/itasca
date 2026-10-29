import Itasca.Runtime.Store.Preparation.Staging
import Itasca.Runtime.Store.Invariant.Syntax
import Itasca.Runtime.Spec.Extend

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

private theorem prefix_lookup {T : Type} (before after : List T)
    (hprefix : after.take before.length = before) (index : Nat) (hi : index < before.length) :
    after[index]? = before[index]? := by
  have h := congrArg (fun xs => xs[index]?) hprefix
  simpa [List.getElem?_take, hi] using h

private theorem prefix_get_d_map {T U : Type} (before after : List T) (f : T → U) (fallback : U)
    (hprefix : after.take before.length = before) (index : Nat) (hi : index < before.length) :
    (after.map f).getD index fallback = (before.map f).getD index fallback := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    prefix_lookup before after hprefix index hi]

/-- Canonical signature insertion does not change the types in an existing
instance's decoded module environment. -/
theorem decode_instance_prefix {M : Type} (before after : runtime.store.Store M)
    (hprefix : StagedPrefix before after) (inst : runtime.store.ModuleInst)
    (hinst : InstanceShape before inst) : decodeInstance after inst = decodeInstance before inst := by
  unfold decodeInstance
  congr 1
  apply List.map_congr_left
  intro index hindex
  exact prefix_get_d_map _ _ decodeFuncType default hprefix.types index.val (hinst.2.2.2.2.2.2.2.1 index hindex)

/-- Existing function instances retain both their signature and defining module
when new objects and canonical signatures are appended during instantiation. -/
theorem decode_function_prefix {M : Type} (code : CodeInterpretation)
    (before after : runtime.store.Store M) (hprefix : StagedPrefix before after)
    (view : M → Slice U8) (shape : Shape view before)
    (function : runtime.store.FuncInst) (hfunction : function ∈ before.funcs.val) :
    decodeFunction code after function = decodeFunction code before function := by
  have hf := shape.functions function hfunction
  unfold decodeFunction
  rw [prefix_get_d_map _ _ decodeFuncType default hprefix.types function.signature.val hf.1]
  cases hc : function.code with
  | Host id => rfl
  | Wasm index fn =>
    have h := hf.2
    simp only [hc] at h
    obtain ⟨inst, hlookup, hfn⟩ := h
    have hib : index.val < before.instances.length := by
      exact List.getElem?_eq_some_iff.mp hlookup |>.1
    have hnew := prefix_lookup before.instances.val after.instances.val hprefix.instances index.val hib
    simp only [hnew, hlookup]
    rw [decode_instance_prefix before after hprefix inst (shape.instances inst (List.mem_of_getElem? hlookup))]

/-- Appending raw store objects preserves every decoded object already present.
The proof includes the indirect dependency of function instances on the
canonical signature pool and defining instance maps. -/
theorem decode_store_prefix {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (before after : runtime.store.Store M) (shape : Shape view before)
    (hprefix : StagedPrefix before after) :
    let old := decodeStore view code before
    let fresh := decodeStore view code after
    fresh.FUNCS.take old.FUNCS.length = old.FUNCS ∧
    fresh.GLOBALS.take old.GLOBALS.length = old.GLOBALS ∧
    fresh.TABLES.take old.TABLES.length = old.TABLES ∧
    fresh.MEMS.take old.MEMS.length = old.MEMS ∧
    fresh.ELEMS.take old.ELEMS.length = old.ELEMS ∧
    fresh.DATAS.take old.DATAS.length = old.DATAS := by
  simp only [decodeStore, List.length_map, ← List.map_take]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hprefix.funcs]
    apply List.map_congr_left
    intro function hfunction
    exact decode_function_prefix code before after hprefix view shape function hfunction
  · rw [hprefix.globals]
  · rw [hprefix.tables]
  · rw [hprefix.memories]
  · rw [hprefix.elems]
  · rw [hprefix.datas]

private theorem prefix_length {T : Type} (before after : List T)
    (hprefix : after.take before.length = before) : before.length ≤ after.length := by
  have h := congrArg List.length hprefix
  simp only [List.length_take] at h
  exact h ▸ Nat.min_le_right _ _

private theorem prefix_get_bang {T : Type} [Inhabited T] (before after : List T)
    (hprefix : after.take before.length = before) (index : Nat) (hi : index < before.length) :
    after[index]! = before[index]! := by
  simp only [List.getElem!_eq_getElem?_getD, prefix_lookup before after hprefix index hi]

private theorem prefix_bounds {T : Type} (before after : List T)
    (hprefix : after.take before.length = before) :
    Forall (fun i => i < after.length) (List.range before.length) := by
  intro i hi
  exact Nat.lt_of_lt_of_le (List.mem_range.mp hi) (prefix_length before after hprefix)

private theorem prefix_rel {T : Type} [Inhabited T] (rel : T → T → Prop) (valid : T → Prop)
    (hrefl : ∀ value, valid value → rel value value) (before after : List T)
    (hprefix : after.take before.length = before) (hvalid : Forall valid before) :
    Forall (fun i => rel before[i]! after[i]!) (List.range before.length) := by
  intro i hi
  have hib := List.mem_range.mp hi
  rw [prefix_get_bang before after hprefix i hib]
  apply hrefl
  simpa only [getElem!_pos before i hib] using hvalid before[i] (List.getElem_mem hib)

/-- Exact retained prefixes are a sufficient concrete case of the specification's
store-extension relation, including its explicit well-formedness obligations. -/
theorem store_prefix_extends (before after : _root_.store)
    (hb : wf_store before) (ha : wf_store after)
    (hf : after.FUNCS.take before.FUNCS.length = before.FUNCS)
    (hg : after.GLOBALS.take before.GLOBALS.length = before.GLOBALS)
    (ht : after.TABLES.take before.TABLES.length = before.TABLES)
    (hm : after.MEMS.take before.MEMS.length = before.MEMS)
    (he : after.ELEMS.take before.ELEMS.length = before.ELEMS)
    (hd : after.DATAS.take before.DATAS.length = before.DATAS) :
    Extend_store before after := by
  have hwf : Forall wf_funcinst before.FUNCS := by cases hb; assumption
  have hwg : Forall wf_globalinst before.GLOBALS := by cases hb; assumption
  have hwt : Forall wf_tableinst before.TABLES := by cases hb; assumption
  have hwm : Forall wf_meminst before.MEMS := by cases hb; assumption
  have hwd : Forall wf_datainst before.DATAS := by cases hb; assumption
  apply Extend_store.mk_Extend_store

  · intro i hi; exact List.mem_range.mp hi
  · exact prefix_bounds before.GLOBALS after.GLOBALS hg
  · exact prefix_rel Extend_globalinst wf_globalinst Spec.extend_global_refl _ _ hg hwg
  · intro i hi; exact List.mem_range.mp hi
  · exact prefix_bounds before.MEMS after.MEMS hm
  · exact prefix_rel Extend_meminst wf_meminst Spec.extend_mem_refl _ _ hm hwm
  · intro i hi; exact List.mem_range.mp hi
  · exact prefix_bounds before.TABLES after.TABLES ht
  · exact prefix_rel Extend_tableinst wf_tableinst Spec.extend_table_refl _ _ ht hwt
  · intro i hi; exact List.mem_range.mp hi
  · exact prefix_bounds before.FUNCS after.FUNCS hf
  · exact prefix_rel Extend_funcinst wf_funcinst Spec.extend_func_refl _ _ hf hwf
  · intro i hi; exact List.mem_range.mp hi
  · exact prefix_bounds before.DATAS after.DATAS hd
  · exact prefix_rel Extend_datainst wf_datainst Spec.extend_data_refl _ _ hd hwd
  · intro i hi; exact List.mem_range.mp hi
  · exact prefix_bounds before.ELEMS after.ELEMS he
  · exact prefix_rel Extend_eleminst (fun _ => True) (fun value _ => Spec.extend_elem_refl value) _ _ he (by simp [Forall])
  · exact hb
  · exact ha

end Itasca.Runtime.Store
