import Itasca.Runtime.Store.Initialization.SegmentReady
import Itasca.Runtime.Store.Invariant.InstantiationCode
import Itasca.Runtime.Store.Api.MemoryBindingLoop
import Itasca.Runtime.Store.Invariant.FunctionTypingExtension
import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.Spec.Integer

/-!
Sections, each formerly its own module: SegmentCodeMetadata, SegmentTypes, SegmentObjectMetadata, SegmentExtension.
-/

/-! ## SegmentCodeMetadata -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Initialization bulk operations retain every function and signature lookup
used by an installed compiler certificate. -/
theorem SegmentAddressSpace.function_table {M : Type} {before after : runtime.store.Store M}
    (metadata : SegmentAddressSpace before after) {inst : runtime.store.ModuleInst} {types : List functype}
    (table : Interp.FunctionTable before inst types) : Interp.FunctionTable after inst types := by
  simpa only [Interp.FunctionTable, metadata.identity, metadata.functions, metadata.signatures] using table

/-- Source start validation and the constructed instance function table resolve
the start function to an owned actual function with no parameters or results. -/
theorem start_function_resolves {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst}
    (table : Interp.FunctionTable store inst (inst.module.module.env.func_types.val.map decodeFuncType))
    (valid : Itasca.ModuleEnv.Valid inst.module.module.env)
    (index : U32) (start : inst.module.module.env.start = some index) :
    ∃ address function signature, inst.funcs.val[index.val]? = some address ∧
      address.store = store.id ∧ store.funcs.val[address.index.val]? = some function ∧
      store.types.val[function.signature.val]? = some signature ∧
      signature.params.val = [] ∧ signature.results.val = [] := by
  obtain ⟨bound, params, results⟩ := valid.start index start
  have rawFound := List.getElem?_eq_getElem bound
  have decodedFound : (inst.module.module.env.func_types.val.map decodeFuncType)[index.val]? =
      some (decodeFuncType inst.module.module.env.func_types.val[index.val]) := by
    simp only [List.getElem?_map, rawFound, Option.map_some]
  obtain ⟨address, function, signature, mapped, owned, found, typed, decoded⟩ := table.resolve index.val _ decodedFound
  have decodedEmpty : decodeFuncType signature = .mk_functype (.mk_list []) (.mk_list []) := by
    simpa only [decodeFuncType, params, results, List.map_nil] using decoded
  have empty : signature.params.val = [] ∧ signature.results.val = [] := by
    simpa only [decodeFuncType, functype.mk_functype.injEq, list.mk_list.injEq,
      List.map_eq_nil_iff] using decodedEmpty
  exact ⟨address, function, signature, mapped, owned, found, typed, empty⟩

end Itasca.Runtime.Store

end

/-! ## SegmentTypes -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The two reference type spaces stay fixed while segment instructions update
only table words and element-segment payloads. -/
structure SegmentTypes {M : Type} (before after : runtime.store.Store M) : Prop where
  tables : after.tables.val.map runtime.store.TableInst.ty = before.tables.val.map runtime.store.TableInst.ty
  elements : after.elems.val.map runtime.store.ElemInst.ty = before.elems.val.map runtime.store.ElemInst.ty

theorem SegmentTypes.refl {M : Type} (store : runtime.store.Store M) : SegmentTypes store store := ⟨rfl, rfl⟩

theorem SegmentTypes.trans {M : Type} {a b c : runtime.store.Store M}
    (ab : SegmentTypes a b) (bc : SegmentTypes b c) : SegmentTypes a c :=
  ⟨bc.tables.trans ab.tables, bc.elements.trans ab.elements⟩

private theorem map_replace_type {T U : Type} (values : List T) (index : Nat) (old value : T)
    (tag : T → U) (found : values[index]? = some old) (same : tag value = tag old) :
    (values.set index value).map tag = values.map tag := by
  induction values generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst old; simp [same]
    | succ index =>
      simp only [List.getElem?_cons_succ] at found
      simpa using ih index found

theorem TableInitializationEffect.types {M : Type} {store : runtime.store.Store M}
    {index table segment destination source count out}
    (effect : TableInitializationEffect store index table segment destination source count out)
    (target : store.tables.val[index.val]? = some table) : SegmentTypes store out.2 := by
  unfold TableInitializationEffect at effect
  split at effect
  · obtain ⟨words, rfl, _⟩ := effect
    constructor
    · simpa only [alloc.vec.Vec.set_val_eq] using map_replace_type store.tables.val index.val table {table with elements := words} runtime.store.TableInst.ty target rfl
    · rfl
  · rw [effect]; exact .refl store

theorem MemoryInitializationEffect.types {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {index memory segment destination source count out}
    (effect : MemoryInitializationEffect view store index memory segment destination source count out) : SegmentTypes store out.2 := by
  unfold MemoryInitializationEffect at effect
  split at effect
  · obtain ⟨buffer, rfl, _⟩ := effect
    exact ⟨rfl, rfl⟩
  · rw [effect]; exact .refl store

theorem SegmentTypes.element_drop {M : Type} (store : runtime.store.Store M) (address : Usize)
    (segment : runtime.store.ElemInst) (found : store.elems.val[address.val]? = some segment) :
    SegmentTypes store {store with elems := store.elems.set address {segment with refs := alloc.vec.Vec.new U64}} := by
  constructor
  · rfl
  · simpa only [alloc.vec.Vec.set_val_eq] using map_replace_type store.elems.val address.val segment {segment with refs := alloc.vec.Vec.new U64}
      runtime.store.ElemInst.ty found rfl

/-- Raw staged table and element types agree with their source index spaces.
This is a link/staging metadata condition, not an interpreter postcondition. -/
structure SegmentTypeBindings {M : Type} (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) : Prop where
  tables : ∀ (index : Nat) (source : Itasca.wasm_types.TableType) (address : runtime.TableAddr) (table : runtime.store.TableInst),
    inst.module.module.env.table_types.val[index]? = some source → inst.tables.val[index]? = some address →
    store.tables.val[address.index.val]? = some table → table.ty = source.elem
  elements : ∀ (index : Nat) (source : Itasca.metadata.Element) (address : Usize) (segment : runtime.store.ElemInst),
    inst.module.module.env.elements.val[index]? = some source → inst.elems.val[index]? = some address →
    store.elems.val[address.val]? = some segment → segment.ty = source.elem

end Itasca.Runtime.Store

end

/-! ## SegmentObjectMetadata -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Exact object metadata retained by initialization; payloads may be copied or dropped. -/
structure SegmentObjectMetadata {M : Type} (view : M → Slice U8)
    (before after : runtime.store.Store M) : Prop where
  space : SegmentAddressSpace before after
  tables : ∀ (index : Nat) (old : runtime.store.TableInst), before.tables.val[index]? = some old → ∃ (next : runtime.store.TableInst),
    after.tables.val[index]? = some next ∧ next.ty = old.ty ∧
    next.maximum = old.maximum ∧ next.elements.length = old.elements.length
  memories : ∀ (index : Nat) (old : runtime.store.MemInst M), before.memories.val[index]? = some old → ∃ (next : runtime.store.MemInst M),
    after.memories.val[index]? = some next ∧ next.maximum = old.maximum ∧
    (view next.buf).length = (view old.buf).length
  elements : ∀ (index : Nat) (old : runtime.store.ElemInst), before.elems.val[index]? = some old → ∃ (next : runtime.store.ElemInst),
    after.elems.val[index]? = some next ∧ next.ty = old.ty ∧
    (next.refs.val = old.refs.val ∨ next.refs.val = [])
  datas : ∀ (index : Nat) (old : runtime.store.DataInst), before.datas.val[index]? = some old → ∃ (next : runtime.store.DataInst),
    after.datas.val[index]? = some next ∧ (next.bytes.val = old.bytes.val ∨ next.bytes.val = [])

theorem SegmentObjectMetadata.refl {M : Type} (view : M → Slice U8) (store : runtime.store.Store M) :
    SegmentObjectMetadata view store store := by
  refine ⟨.refl _, ?_, ?_, ?_, ?_⟩
  · intro i old found; exact ⟨old, found, rfl, rfl, rfl⟩
  · intro i old found; exact ⟨old, found, rfl, rfl⟩
  · intro i old found; exact ⟨old, found, rfl, Or.inl rfl⟩
  · intro i old found; exact ⟨old, found, Or.inl rfl⟩

theorem SegmentObjectMetadata.trans {M : Type} {view : M → Slice U8} {a b c : runtime.store.Store M}
    (ab : SegmentObjectMetadata view a b) (bc : SegmentObjectMetadata view b c) :
    SegmentObjectMetadata view a c := by
  refine ⟨ab.space.trans bc.space, ?_, ?_, ?_, ?_⟩
  · intro i old found
    obtain ⟨mid, middle, ty, max, len⟩ := ab.tables i old found
    obtain ⟨next, last, ty', max', len'⟩ := bc.tables i mid middle
    exact ⟨next, last, ty'.trans ty, max'.trans max, len'.trans len⟩
  · intro i old found
    obtain ⟨mid, middle, max, len⟩ := ab.memories i old found
    obtain ⟨next, last, max', len'⟩ := bc.memories i mid middle
    exact ⟨next, last, max'.trans max, len'.trans len⟩
  · intro i old found
    obtain ⟨mid, middle, ty, content⟩ := ab.elements i old found
    obtain ⟨next, last, ty', content'⟩ := bc.elements i mid middle
    refine ⟨next, last, ty'.trans ty, ?_⟩
    rcases content' with same | empty
    · rcases content with original | dropped
      · exact Or.inl (same.trans original)
      · exact Or.inr (same.trans dropped)
    · exact Or.inr empty
  · intro i old found
    obtain ⟨mid, middle, content⟩ := ab.datas i old found
    obtain ⟨next, last, content'⟩ := bc.datas i mid middle
    refine ⟨next, last, ?_⟩
    rcases content' with same | empty
    · rcases content with original | dropped
      · exact Or.inl (same.trans original)
      · exact Or.inr (same.trans dropped)
    · exact Or.inr empty

theorem lookup_set_relation {T : Type} (values : List T) (index : Nat) (old replacement : T)
    (found : values[index]? = some old) (R : T → T → Prop)
    (refl : ∀ value, R value value) (changed : R old replacement) :
    ∀ (i : Nat) value, values[i]? = some value → ∃ next, (values.set index replacement)[i]? = some next ∧ R value next := by
  intro i value read
  by_cases same : i = index
  · subst i
    have equal : value = old := Option.some.inj (read.symm.trans found)
    subst value
    exact ⟨replacement, by simp [List.getElem?_set, (List.getElem?_eq_some_iff.mp found).1], changed⟩
  · exact ⟨value, by simp [List.getElem?_set, same, Ne.symm same, read], refl value⟩

end Itasca.Runtime.Store

end

/-! ## SegmentExtension -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

private theorem mapped_objects {A B : Type} [Inhabited B] (f : A → B)
    (R : B → B → Prop) (xs ys : List A) (lengths : xs.length ≤ ys.length)
    (objects : ∀ (index : Nat) (old : A), xs[index]? = some old → ∃ fresh,
      ys[index]? = some fresh ∧ R (f old) (f fresh)) :
    Spec.ObjectsExtend R (xs.map f) (ys.map f) := by
  refine ⟨by simpa only [List.length_map] using lengths, ?_⟩
  intro index bound
  have room : index < xs.length := by simpa only [List.length_map] using bound
  have found : xs[index]? = some xs[index] := List.getElem?_eq_getElem room
  obtain ⟨fresh, lookup, relation⟩ := objects index xs[index] found
  simpa only [List.getElem!_eq_getElem?_getD, List.getElem?_map, found, lookup,
    Option.map_some, Option.getD_some] using relation

private theorem table_extension (before after : runtime.store.TableInst)
    (ty : after.ty = before.ty) (maximum : after.maximum = before.maximum)
    (length : after.elements.length = before.elements.length)
    (old : wf_tableinst (decodeTable before)) (fresh : wf_tableinst (decodeTable after)) :
    Extend_tableinst (decodeTable before) (decodeTable after) := by
  unfold decodeTable at old fresh ⊢
  rw [ty, maximum, length] at fresh ⊢
  simp only [decode_limits_option] at old fresh ⊢
  exact .mk_Extend_tableinst _ _ _ _ _ _ (Nat.le_refl _)
    (by simpa only [List.length_map] using length.ge) old fresh

private theorem memory_extension {M : Type} (view : M → Slice U8) (before after : runtime.store.MemInst M)
    (maximum : after.maximum = before.maximum) (length : (view after.buf).length = (view before.buf).length)
    (old : wf_meminst (decodeMemory view before)) (fresh : wf_meminst (decodeMemory view after)) :
    Extend_meminst (decodeMemory view before) (decodeMemory view after) := by
  unfold decodeMemory at old fresh ⊢
  rw [maximum, length] at fresh ⊢
  simp only [decode_limits_option] at old fresh ⊢
  exact .mk_Extend_meminst _ _ _ _ _ (Nat.le_refl _)
    (by simpa only [decodeBytes, List.length_map] using length.ge) old fresh

private theorem element_extension (before after : runtime.store.ElemInst)
    (ty : after.ty = before.ty) (contents : after.refs.val = before.refs.val ∨ after.refs.val = []) :
    Extend_eleminst (decodeElement before) (decodeElement after) := by
  unfold decodeElement
  rw [ty]
  apply Extend_eleminst.mk_Extend_eleminst
  rcases contents with same | empty
  · exact Or.inl (by rw [same])
  · exact Or.inr (by rw [empty]; rfl)

private theorem data_extension (before after : runtime.store.DataInst)
    (contents : after.bytes.val = before.bytes.val ∨ after.bytes.val = [])
    (old : wf_datainst (decodeData before)) (fresh : wf_datainst (decodeData after)) :
    Extend_datainst (decodeData before) (decodeData after) := by
  apply Extend_datainst.mk_Extend_datainst _ _ _ old fresh
  rcases contents with same | empty
  · exact Or.inl (by simp only [decodeBytes, same])
  · exact Or.inr (by simp only [decodeBytes, empty, List.map_nil])

/-- Actual initialization metadata implies generated store extension. Memory
and table writes preserve limits; segment drops are permitted by the generated
relation. No function body or signature is changed. -/
theorem SegmentObjectMetadata.extends {M : Type} {view : M → Slice U8}
    {before after : runtime.store.Store M} (metadata : SegmentObjectMetadata view before after)
    (code : CodeInterpretation)
    (oldWf : wf_store (decodeStore view code before))
    (freshWf : wf_store (decodeStore view code after)) :
    Extend_store (decodeStore view code before) (decodeStore view code after) := by
  have oldFunctions : Forall wf_funcinst (decodeStore view code before).FUNCS := by cases oldWf; assumption
  have oldGlobals : Forall wf_globalinst (decodeStore view code before).GLOBALS := by cases oldWf; assumption
  have oldTables : Forall wf_tableinst (decodeStore view code before).TABLES := by cases oldWf; assumption
  have freshTables : Forall wf_tableinst (decodeStore view code after).TABLES := by cases freshWf; assumption
  have oldMemories : Forall wf_meminst (decodeStore view code before).MEMS := by cases oldWf; assumption
  have freshMemories : Forall wf_meminst (decodeStore view code after).MEMS := by cases freshWf; assumption
  have oldDatas : Forall wf_datainst (decodeStore view code before).DATAS := by cases oldWf; assumption
  have freshDatas : Forall wf_datainst (decodeStore view code after).DATAS := by cases freshWf; assumption
  obtain ⟨globals, _, _, functions, _, _⟩ := Spec.extend_store_objects (Spec.extend_store_refl _ oldWf)
  apply Spec.extend_store_of_objects oldWf freshWf
  · simpa only [decodeStore, metadata.space.globals] using globals
  · apply mapped_objects (decodeMemory view) Extend_meminst before.memories.val after.memories.val metadata.space.memories.ge
    intro index old found
    obtain ⟨fresh, lookup, maximum, length⟩ := metadata.memories index old found
    exact ⟨fresh, lookup, memory_extension view old fresh maximum length
      (oldMemories _ (List.mem_map.mpr ⟨old, List.mem_of_getElem? found, rfl⟩))
      (freshMemories _ (List.mem_map.mpr ⟨fresh, List.mem_of_getElem? lookup, rfl⟩))⟩
  · apply mapped_objects decodeTable Extend_tableinst before.tables.val after.tables.val metadata.space.tables.ge
    intro index old found
    obtain ⟨fresh, lookup, ty, maximum, length⟩ := metadata.tables index old found
    exact ⟨fresh, lookup, table_extension old fresh ty maximum length
      (oldTables _ (List.mem_map.mpr ⟨old, List.mem_of_getElem? found, rfl⟩))
      (freshTables _ (List.mem_map.mpr ⟨fresh, List.mem_of_getElem? lookup, rfl⟩))⟩
  · rw [metadata.space.decoded_functions view code]
    exact functions
  · apply mapped_objects decodeData Extend_datainst before.datas.val after.datas.val metadata.space.datas.ge
    intro index old found
    obtain ⟨fresh, lookup, contents⟩ := metadata.datas index old found
    exact ⟨fresh, lookup, data_extension old fresh contents
      (oldDatas _ (List.mem_map.mpr ⟨old, List.mem_of_getElem? found, rfl⟩))
      (freshDatas _ (List.mem_map.mpr ⟨fresh, List.mem_of_getElem? lookup, rfl⟩))⟩
  · apply mapped_objects decodeElement Extend_eleminst before.elems.val after.elems.val metadata.space.elements.ge
    intro index old found
    obtain ⟨fresh, lookup, ty, contents⟩ := metadata.elements index old found
    exact ⟨fresh, lookup, element_extension old fresh ty contents⟩

/-- Retained or dropped payloads preserve the binary segment length bounds. -/
theorem SegmentObjectMetadata.segment_bounds {M : Type} {view : M → Slice U8}
    {before after : runtime.store.Store M} (metadata : SegmentObjectMetadata view before after)
    (bounds : SegmentBounds before) : SegmentBounds after := by
  constructor
  · intro element member
    obtain ⟨index, bound, equal⟩ := List.mem_iff_getElem.mp member
    have oldBound : index < before.elems.length := by simpa only [metadata.space.elements] using bound
    have oldFound : before.elems.val[index]? = some before.elems.val[index] := List.getElem?_eq_getElem oldBound
    obtain ⟨fresh, found, _, contents⟩ := metadata.elements index before.elems.val[index] oldFound
    have same : fresh = element := by
      have read : after.elems.val[index]? = some element := List.getElem?_eq_some_iff.mpr ⟨bound, equal⟩
      exact Option.some.inj (found.symm.trans read)
    subst fresh
    have oldLength := bounds.elements before.elems.val[index] (List.mem_of_getElem? oldFound)
    change element.refs.val.length < _
    rcases contents with retained | dropped
    · rw [retained]; exact oldLength
    · simp only [dropped, List.length_nil]; norm_num
  · intro segment member
    obtain ⟨index, bound, equal⟩ := List.mem_iff_getElem.mp member
    have oldBound : index < before.datas.length := by simpa only [metadata.space.datas] using bound
    have oldFound : before.datas.val[index]? = some before.datas.val[index] := List.getElem?_eq_getElem oldBound
    obtain ⟨fresh, found, contents⟩ := metadata.datas index before.datas.val[index] oldFound
    have same : fresh = segment := by
      have read : after.datas.val[index]? = some segment := List.getElem?_eq_some_iff.mpr ⟨bound, equal⟩
      exact Option.some.inj (found.symm.trans read)
    subst fresh
    have oldLength := bounds.data before.datas.val[index] (List.mem_of_getElem? oldFound)
    change segment.bytes.val.length < _
    rcases contents with retained | dropped
    · rw [retained]; exact oldLength
    · simp only [dropped, List.length_nil]; norm_num

end Itasca.Runtime.Store

end
