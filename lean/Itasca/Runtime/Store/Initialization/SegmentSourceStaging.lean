import Itasca.Runtime.Store.Initialization.SegmentReady
import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Store.Api.ObjectStaging
import Itasca.Runtime.Store.Invariant.HostSignature
import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.Spec.TypingAndNumericOperations
import Itasca.Generated.Funs
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Store.Initialization.SegmentOperations
import Itasca.Runtime.Store.Api.GlobalStagingAndCopy
import Itasca.Runtime.Compiler.Local.Initializer
import Itasca.Runtime.Store.Initialization.DataEffects
import Itasca.Runtime.Store.Definitions
import Itasca.Generated.Types
import Itasca.Runtime.Compiler.Local.Relations.Function.RootLabel

/-!
Proofs for Runtime / Store / Initialization.

This module collects SegmentExtension, ElementTypedEffect, ElementShapeLoop, SegmentSourceStaging.
Each section documents its contracts and consumers.
-/

/-! ## SegmentExtension -/

section

/-!
Proofs for Runtime / Store / Initialization.

This module collects SegmentExtension, SegmentObjectEffects.
Each section documents its contracts and consumers.
-/

/-! ## SegmentExtension -/

section

open Itasca.Representation

/-! ## SegmentCodeMetadata -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- Initialization bulk operations retain every function and signature lookup
used by an installed compiler certificate. -/
theorem SegmentAddressSpace.function_table {M : Type} {before after : runtime.store.Store M}
    (metadata : SegmentAddressSpace before after) {inst : runtime.store.ModuleInst} {types : List functype}
    (table : Representation.FunctionTable before inst types) : Representation.FunctionTable after inst types := by
  simpa only [Representation.FunctionTable, metadata.identity, metadata.functions, metadata.signatures] using table

/-- Source start validation and the constructed instance function table resolve
the start function to an owned actual function with no parameters or results. -/
theorem start_function_resolves {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst}
    (table : Representation.FunctionTable store inst (inst.module.module.env.func_types.val.map Itasca.Translation.Environment.funcType))
    (valid : Itasca.Module.Environment.Valid inst.module.module.env)
    (index : U32) (start : inst.module.module.env.start = some index) :
    ∃ address function signature, inst.funcs.val[index.val]? = some address ∧
      address.store = store.id ∧ store.funcs.val[address.index.val]? = some function ∧
      store.types.val[function.signature.val]? = some signature ∧
      signature.params.val = [] ∧ signature.results.val = [] := by
  obtain ⟨bound, params, results⟩ := valid.start index start
  have rawFound := List.getElem?_eq_getElem bound
  have decodedFound : (inst.module.module.env.func_types.val.map Itasca.Translation.Environment.funcType)[index.val]? =
      some (Itasca.Translation.Environment.funcType inst.module.module.env.func_types.val[index.val]) := by
    simp only [List.getElem?_map, rawFound, Option.map_some]
  obtain ⟨address, function, signature, mapped, owned, found, typed, decoded⟩ := table.resolve index.val _ decodedFound
  have decodedEmpty : Itasca.Translation.Environment.funcType signature = .mk_functype (.mk_list []) (.mk_list []) := by
    simpa only [Itasca.Translation.Environment.funcType, params, results, List.map_nil] using decoded
  have empty : signature.params.val = [] ∧ signature.results.val = [] := by
    simpa only [Itasca.Translation.Environment.funcType, functype.mk_functype.injEq, list.mk_list.injEq,
      List.map_eq_nil_iff] using decodedEmpty
  exact ⟨address, function, signature, mapped, owned, found, typed, empty⟩

end Itasca.Store

end

/-! ## SegmentTypes -/

section

namespace Itasca.Store
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

end Itasca.Store

end

/-! ## SegmentObjectMetadata -/

section

namespace Itasca.Store
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

end Itasca.Store

end

/-! ## SegmentExtension -/

section

namespace Itasca.Store
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

end Itasca.Store

end

end

/-! ## SegmentObjectEffects -/

section

open Itasca.Representation

/-! ## SegmentCompatible -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- For an emitted table initialization, source-segment words and destination
slots have the same reference type. Other instructions impose no type equality. -/
def SegmentBulkCompatible {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) : Prop :=
  match instruction with
  | .TableInit _ entry => ∀ element tableId address target segment table,
      code.indirect.val[entry.val]? = some (element, tableId) →
      inst.elems.val[element.val]? = some address → inst.tables.val[tableId.val]? = some target →
      store.elems.val[address.val]? = some segment → store.tables.val[target.index.val]? = some table →
      segment.ty = table.ty
  | _ => True

theorem SegmentBulkCompatible.transport {M : Type} {store after : runtime.store.Store M}
    {inst code instruction} (compatible : SegmentBulkCompatible store inst code instruction)
    (same : SegmentTypes store after) : SegmentBulkCompatible after inst code instruction := by
  cases instruction <;> simp only [SegmentBulkCompatible] at compatible ⊢
  all_goals try trivial
  intro element tableId address target segment table descriptor mapped tableMapped sourceFound targetFound
  have elementTags := congrArg (fun values : List Itasca.wasm_types.ElemType => values[address.val]?) same.elements
  have tableTags := congrArg (fun values : List Itasca.wasm_types.ElemType => values[target.index.val]?) same.tables
  simp only [List.getElem?_map, sourceFound, Option.map_some] at elementTags
  simp only [List.getElem?_map, targetFound, Option.map_some] at tableTags
  cases oldSource : store.elems.val[address.val]? with
  | none => simp [oldSource] at elementTags
  | some oldSegment =>
    cases oldTarget : store.tables.val[target.index.val]? with
    | none => simp [oldTarget] at tableTags
    | some oldTable =>
      have sourceType : segment.ty = oldSegment.ty := by simpa [oldSource] using elementTags
      have targetType : table.ty = oldTable.ty := by simpa [oldTarget] using tableTags
      rw [sourceType, targetType]
      exact compatible element tableId address target oldSegment oldTable descriptor mapped tableMapped oldSource oldTarget

/-- Source typing and source/raw type-map agreement establish the needed equality
for a compiler-selected active element segment. -/
theorem segment_table_compatible {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (entry element tableId : U32) (segment : Itasca.metadata.Element) (tableType : Itasca.wasm_types.TableType)
    (descriptor : code.indirect.val[entry.val]? = some (element, tableId))
    (source : inst.module.module.env.elements.val[element.val]? = some segment)
    (target : inst.module.module.env.table_types.val[tableId.val]? = some tableType)
    (same : segment.elem = tableType.elem) (bindings : SegmentTypeBindings store inst) :
    SegmentBulkCompatible store inst code (.TableInit 0#u32 entry) := by
  intro actualElement actualTable address tableAddress values table actualDescriptor mapped tableMapped valuesFound tableFound
  have pair := Option.some.inj (actualDescriptor.symm.trans descriptor)
  have first := congrArg Prod.fst pair
  have second := congrArg Prod.snd pair
  dsimp only at first second
  subst actualElement actualTable
  rw [bindings.elements element.val segment address values source mapped valuesFound,
    bindings.tables tableId.val tableType tableAddress table target tableMapped tableFound, same]

end Itasca.Store

end

/-! ## SegmentObjectEffects -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

theorem TableInitializationEffect.object_metadata {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {index table segment destination source count out}
    (effect : TableInitializationEffect store index table segment destination source count out)
    (target : store.tables.val[index.val]? = some table) : SegmentObjectMetadata view store out.2 := by
  unfold TableInitializationEffect at effect
  split at effect
  · obtain ⟨words, rfl, values⟩ := effect
    have length : words.length = table.elements.length := by
      simpa only [alloc.vec.Vec.length] using (congrArg List.length values).trans (copy_segment_length _ _ _ _ _)
    refine ⟨by constructor <;> simp, ?_, ?_, ?_, ?_⟩
    · simpa only [alloc.vec.Vec.set_val_eq] using lookup_set_relation store.tables.val index.val table
        {table with elements := words} target
        (fun old next => next.ty = old.ty ∧ next.maximum = old.maximum ∧ next.elements.length = old.elements.length)
        (fun _ => ⟨rfl,rfl,rfl⟩) ⟨rfl,rfl,length⟩
    · intro i old found; exact ⟨old, found, rfl,rfl⟩
    · intro i old found; exact ⟨old, found, rfl,Or.inl rfl⟩
    · intro i old found; exact ⟨old, found, Or.inl rfl⟩
  · rw [effect]; exact .refl _ _

theorem MemoryInitializationEffect.object_metadata {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {index memory segment destination source count out}
    (effect : MemoryInitializationEffect view store index memory segment destination source count out)
    (target : store.memories.val[index.val]? = some memory) : SegmentObjectMetadata view store out.2 := by
  unfold MemoryInitializationEffect at effect
  split at effect
  · obtain ⟨buffer, rfl, values⟩ := effect
    have length : (view buffer).length = (view memory.buf).length := by
      simpa only [List.length_setSlice!] using congrArg List.length values
    refine ⟨by constructor <;> simp, ?_, ?_, ?_, ?_⟩
    · intro i old found; exact ⟨old, found, rfl,rfl,rfl⟩
    · simpa only [alloc.vec.Vec.set_val_eq] using lookup_set_relation store.memories.val index.val memory
        {memory with buf := buffer} target
        (fun old next => next.maximum = old.maximum ∧ (view next.buf).length = (view old.buf).length)
        (fun _ => ⟨rfl,rfl⟩) ⟨rfl,length⟩
    · intro i old found; exact ⟨old, found, rfl,Or.inl rfl⟩
    · intro i old found; exact ⟨old, found, Or.inl rfl⟩
  · rw [effect]; exact .refl _ _

theorem SegmentObjectMetadata.data_drop {M : Type} (view : M → Slice U8)
    (store : runtime.store.Store M) (index : Usize) (old : runtime.store.DataInst)
    (target : store.datas.val[index.val]? = some old) :
    SegmentObjectMetadata view store {store with datas := store.datas.set index ⟨alloc.vec.Vec.new U8⟩} := by
  refine ⟨by constructor <;> simp, ?_, ?_, ?_, ?_⟩
  · intro i old found; exact ⟨old, found, rfl,rfl,rfl⟩
  · intro i old found; exact ⟨old, found, rfl,rfl⟩
  · intro i old found; exact ⟨old, found, rfl,Or.inl rfl⟩
  · simpa only [alloc.vec.Vec.set_val_eq] using lookup_set_relation store.datas.val index.val old
      ⟨alloc.vec.Vec.new U8⟩ target
      (fun old next => next.bytes.val = old.bytes.val ∨ next.bytes.val = [])
      (fun _ => Or.inl rfl) (Or.inr rfl)

theorem SegmentObjectMetadata.element_drop {M : Type} (view : M → Slice U8)
    (store : runtime.store.Store M) (index : Usize) (old : runtime.store.ElemInst)
    (target : store.elems.val[index.val]? = some old) :
    SegmentObjectMetadata view store {store with elems := store.elems.set index {old with refs := alloc.vec.Vec.new U64}} := by
  refine ⟨by constructor <;> simp, ?_, ?_, ?_, ?_⟩
  · intro i old found; exact ⟨old, found, rfl,rfl,rfl⟩
  · intro i old found; exact ⟨old, found, rfl,rfl⟩
  · simpa only [alloc.vec.Vec.set_val_eq] using lookup_set_relation store.elems.val index.val old
      {old with refs := alloc.vec.Vec.new U64} target
      (fun old next => next.ty = old.ty ∧ (next.refs.val = old.refs.val ∨ next.refs.val = []))
      (fun _ => ⟨rfl,Or.inl rfl⟩) ⟨rfl,Or.inr rfl⟩
  · intro i old found; exact ⟨old, found, Or.inl rfl⟩

end Itasca.Store

end

end

end

/-! ## ElementTypedEffect -/

section

/-!
Proofs for Runtime / Store / Initialization.

This module collects ElementTypedEffect, ElementTypes.
Each section documents its contracts and consumers.
-/

/-! ## ElementTypedEffect -/

section

/-! ## ElementEffects -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

inductive ElementStageEffect {M : Type} (store : runtime.store.Store M)
    (instIndex : Usize) (inst : runtime.store.ModuleInst) : runtime.store.Store M → Prop where
  | unchanged : ElementStageEffect store instIndex inst store
  | appended (elements : alloc.vec.Vec runtime.store.ElemInst)
      (addresses : alloc.vec.Vec Usize) (element : runtime.store.ElemInst)
      (elementValues : elements.val = store.elems.val ++ [element])
      (addressValues : addresses.val = inst.elems.val ++ [store.elems.len]) :
      ElementStageEffect store instIndex inst
        { store with elems := elements, instances := store.instances.set instIndex { inst with elems := addresses } }

theorem add_instance_element_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.ModuleInst) (segment : Itasca.metadata.Element)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (helem : inst.module.module.env.elements.val[index.val]? = some segment)
    (certificates : ElementInitializers store inst index segment)
    (bindings : InitializerBindings store inst)
    (room : store.elems.length < Usize.max) (mapRoom : inst.elems.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_element memory hooks floats allocator store platform instIndex index
      ⦃ out => ElementStageEffect store instIndex inst out.2.1 ∧ out.2.2 = platform ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_element
  step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Env.impl.elements, bind_ok]
  step with Itasca.Representation.slice_index_given inst.module.module.env.elements.deref index segment
    (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
  subst found
  obtain ⟨reserved, hreserve⟩ := reserve_wrapper_eq allocator law (alloc.vec.Vec.new U64) segment.init.len
  rw [hreserve]
  cases reserved with
  | false =>
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementStageEffect.unchanged (store := store) (instIndex := instIndex) (inst := inst))
  | true =>
    simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with element_initializers_loop memory hooks floats allocator law store platform instIndex index
      segment.init.len inst segment hi helem (by simp) certificates bindings
      (alloc.vec.Vec.new U64) 0#usize (.Ok ()) (by simp) (by scalar_tac)
      as ⟨after, host, values, status, hs, hp, hvalues⟩
    subst after host
    cases status with
    | Err error =>
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementStageEffect.unchanged (store := store) (instIndex := instIndex) (inst := inst))
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨reserved, hreserve⟩ := reserve_wrapper_eq allocator law store.elems 1#usize
      rw [hreserve]
      cases reserved with
      | false =>
        simpa [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementStageEffect.unchanged (store := store) (instIndex := instIndex) (inst := inst))
      | true =>
        simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
        subst found
        step with Itasca.Representation.slice_index_given inst.module.module.env.elements.deref index segment
          (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
        subst found
        step as ⟨elements, helements⟩
        have instanceBound : instIndex.val < store.instances.length :=
          (List.getElem?_eq_some_iff.mp hi).1
        step as ⟨old, back, hold, hback⟩
        have old_eq : old = inst := by
          have hread := List.getElem?_eq_getElem instanceBound
          rw [hi] at hread
          exact hold.trans (Option.some.inj hread).symm
        subst old
        step as ⟨addresses, haddresses⟩
        have instanceRead : store.instances.val[instIndex.val] = inst :=
          Option.some.inj ((List.getElem?_eq_getElem instanceBound).symm.trans hi)
        have effect := ElementStageEffect.appended (store := store) (instIndex := instIndex) (inst := inst)
          elements addresses {ty := segment.elem, refs := values} helements
          (by simpa only [instanceRead] using haddresses)
        simpa [hback, instanceRead] using And.intro effect (rfl : platform = platform)

theorem ElementStageEffect.context {M : Type} {store after : runtime.store.Store M}
    {instIndex : Usize} {inst : runtime.store.ModuleInst}
    (effect : ElementStageEffect store instIndex inst after)
    (found : store.instances.val[instIndex.val]? = some inst)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst) :
    ∃ next, after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
      InitializerBindings after next ∧ InitializerImports after next ∧
      InitializerSegmentBindings after next ∧ next.elems.length ≤ inst.elems.length + 1 ∧
      after.elems.length ≤ store.elems.length + 1 ∧ next.datas = inst.datas := by
  cases effect with
  | unchanged => exact ⟨inst, found, rfl, bindings, imports, segments, by omega, by omega, rfl⟩
  | appended elements addresses element elementValues addressValues =>
    have bound : instIndex.val < store.instances.val.length := (List.getElem?_eq_some_iff.mp found).1
    refine ⟨{inst with elems := addresses}, ?_, rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · simp [alloc.vec.Vec.set_val_eq, bound]
    · exact ⟨bindings.funcs, bindings.globals⟩
    · exact imports.extend rfl rfl (by simp) (by simp)
    · exact ⟨segments.tableCount, segments.memoryCount, segments.tables, segments.memories⟩
    · simp [addressValues]
    · simp [elementValues]

theorem ElementStageEffect.data {M : Type} {store after : runtime.store.Store M}
    {instIndex : Usize} {inst : runtime.store.ModuleInst}
    (effect : ElementStageEffect store instIndex inst after) : after.datas = store.datas := by
  cases effect <;> rfl

theorem ElementStageEffect.object_count {M : Type} {store after : runtime.store.Store M}
    {instIndex : Usize} {inst : runtime.store.ModuleInst}
    (effect : ElementStageEffect store instIndex inst after) : objectCount after = objectCount store := by
  cases effect <;> rfl

theorem ElementStageEffect.staged {M : Type} {before store after : runtime.store.Store M}
    {instIndex : Usize} {inst : runtime.store.ModuleInst}
    (effect : ElementStageEffect store instIndex inst after)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val) :
    StagedPrefix before after := by
  cases effect with
  | unchanged => exact staged
  | appended elements addresses element elementValues addressValues =>
    have appended : StagedPrefix store {store with elems := elements} := by
      constructor <;> simp [elementValues]
    exact (staged.trans appended).set_fresh_instance instIndex {inst with elems := addresses} fresh

end Itasca.Store

end

/-! ## ElementTypedEffect -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- Exact element staging retains the source reference type in the newly
allocated segment and distinguishes a normal refusal from successful append. -/
inductive ElementTypedEffect {M : Type} (store : runtime.store.Store M)
    (instIndex : Usize) (inst : runtime.store.ModuleInst) (source : Itasca.metadata.Element) :
    core.result.Result Unit runtime.ExecError → runtime.store.Store M → Prop where
  | failed (error : runtime.ExecError) : ElementTypedEffect store instIndex inst source (.Err error) store
  | appended (elements : alloc.vec.Vec runtime.store.ElemInst) (addresses : alloc.vec.Vec Usize)
      (values : alloc.vec.Vec U64)
      (elementValues : elements.val = store.elems.val ++ [{ty := source.elem, refs := values}])
      (addressValues : addresses.val = inst.elems.val ++ [store.elems.len]) :
      ElementTypedEffect store instIndex inst source (.Ok ())
        {store with elems := elements, instances := store.instances.set instIndex {inst with elems := addresses}}

theorem ElementTypedEffect.effect {M : Type} {store after : runtime.store.Store M}
    {instIndex inst source status} (typed : ElementTypedEffect store instIndex inst source status after) :
    ElementStageEffect store instIndex inst after := by
  cases typed with
  | failed error => exact .unchanged
  | appended elements addresses values stored mapped => exact .appended elements addresses _ stored mapped

theorem add_instance_element_typed_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.ModuleInst) (segment : Itasca.metadata.Element)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (helem : inst.module.module.env.elements.val[index.val]? = some segment)
    (certificates : ElementInitializers store inst index segment)
    (bindings : InitializerBindings store inst)
    (room : store.elems.length < Usize.max) (mapRoom : inst.elems.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_element memory hooks floats allocator store platform instIndex index
      ⦃ out => ElementTypedEffect store instIndex inst segment out.1 out.2.1 ∧ out.2.2 = platform ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_element
  step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Env.impl.elements, bind_ok]
  step with Itasca.Representation.slice_index_given inst.module.module.env.elements.deref index segment
    (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
  subst found
  obtain ⟨reserved, hreserve⟩ := reserve_wrapper_eq allocator law (alloc.vec.Vec.new U64) segment.init.len
  rw [hreserve]
  cases reserved with
  | false =>
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementTypedEffect.failed (store := store) (instIndex := instIndex) (inst := inst) (source := segment) (.Exhausted .Allocation))
  | true =>
    simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with element_initializers_loop memory hooks floats allocator law store platform instIndex index
      segment.init.len inst segment hi helem (by simp) certificates bindings
      (alloc.vec.Vec.new U64) 0#usize (.Ok ()) (by simp) (by scalar_tac)
      as ⟨after, host, values, status, hs, hp, hvalues⟩
    subst after host
    cases status with
    | Err error =>
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementTypedEffect.failed (store := store) (instIndex := instIndex) (inst := inst) (source := segment) error)
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨reserved, hreserve⟩ := reserve_wrapper_eq allocator law store.elems 1#usize
      rw [hreserve]
      cases reserved with
      | false =>
        simpa [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementTypedEffect.failed (store := store) (instIndex := instIndex) (inst := inst) (source := segment) (.Exhausted .Allocation))
      | true =>
        simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
        subst found
        step with Itasca.Representation.slice_index_given inst.module.module.env.elements.deref index segment
          (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
        subst found
        step as ⟨elements, helements⟩
        have instanceBound : instIndex.val < store.instances.length :=
          (List.getElem?_eq_some_iff.mp hi).1
        step as ⟨old, back, hold, hback⟩
        have old_eq : old = inst := by
          have hread := List.getElem?_eq_getElem instanceBound
          rw [hi] at hread
          exact hold.trans (Option.some.inj hread).symm
        subst old
        step as ⟨addresses, haddresses⟩
        have instanceRead : store.instances.val[instIndex.val] = inst :=
          Option.some.inj ((List.getElem?_eq_getElem instanceBound).symm.trans hi)
        have effect := ElementTypedEffect.appended (store := store) (instIndex := instIndex) (inst := inst) (source := segment)
          elements addresses values helements
          (by simpa only [instanceRead] using haddresses)
        simpa [hback, instanceRead] using And.intro effect (rfl : platform = platform)

end Itasca.Store

end

end

/-! ## ElementTypes -/

section

/-!
# Element type maps

Element initializer effects retain the correspondence between staged element values, addresses and source types. Data staging preserves that correspondence through both success and refusal.
-/

namespace Itasca.Store
open Aeneas Aeneas.Std

def ElementTypeMap {M : Type} (store : runtime.store.Store M)
    (source : List Itasca.metadata.Element) (addresses : List Usize) : Prop :=
  List.Forall₂ (fun entry address => ∃ segment, store.elems.val[address.val]? = some segment ∧ segment.ty = entry.elem) source addresses

theorem ElementTypeMap.prefix {M : Type} {store after : runtime.store.Store M} {source addresses}
    (matching : ElementTypeMap store source addresses) (retained : after.elems.val.take store.elems.length = store.elems.val) :
    ElementTypeMap after source addresses := by
  apply matching.imp
  rintro entry address ⟨segment, found, equal⟩
  refine ⟨segment, ?_, equal⟩
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have lookup := congrArg (fun values : List runtime.store.ElemInst => values[address.val]?) retained
  simp only [List.getElem?_take, alloc.vec.Vec.length, if_pos bound] at lookup
  exact lookup.trans found

theorem ElementTypedEffect.type_map {M : Type} {store after : runtime.store.Store M}
    {inst next : runtime.store.ModuleInst} {instIndex : Usize} {source status}
    (effect : ElementTypedEffect store instIndex inst source status after)
    (bound : instIndex.val < store.instances.length)
    (found : after.instances.val[instIndex.val]? = some next)
    {entries : List Itasca.metadata.Element} (matching : ElementTypeMap store entries inst.elems.val)
    (success : status = .Ok ()) : ElementTypeMap after (entries ++ [source]) next.elems.val := by
  cases effect with
  | failed error => simp at success
  | appended elements addresses values stored mapped =>
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at found
    subst next
    have old := matching.prefix (after := {store with elems := elements, instances := store.instances.set instIndex {inst with elems := addresses}})
      (by simp [stored])
    change List.Forall₂ _ _ addresses.val
    rw [mapped]
    apply List.rel_append old
    exact .cons ⟨{ty := source.elem, refs := values}, by simp [stored], rfl⟩ .nil

theorem ElementTypeMap.bindings {M : Type} {store : runtime.store.Store M} {inst : runtime.store.ModuleInst}
    (matching : ElementTypeMap store inst.module.module.env.elements.val inst.elems.val) :
    ∀ (index : Nat) (source : Itasca.metadata.Element) (address : Usize) (segment : runtime.store.ElemInst),
      inst.module.module.env.elements.val[index]? = some source → inst.elems.val[index]? = some address →
      store.elems.val[address.val]? = some segment → segment.ty = source.elem := by
  intro index source address segment sourceFound mapped found
  have left := (List.getElem?_eq_some_iff.mp sourceFound).1
  have right := (List.getElem?_eq_some_iff.mp mapped).1
  have related := matching.get left right
  simp only [List.get_eq_getElem] at related
  have sourceEq := (List.getElem?_eq_some_iff.mp sourceFound).2
  have addressEq := (List.getElem?_eq_some_iff.mp mapped).2
  rw [sourceEq, addressEq] at related
  obtain ⟨actual, actualFound, typed⟩ := related
  have same : actual = segment := Option.some.inj (actualFound.symm.trans found)
  simpa only [same] using typed

/-- Data staging changes no element values or element addresses, including
refusal branches before or after a data append. -/
theorem DataStageEffect.element_types {M : Type} {store after : runtime.store.Store M}
    {inst next : runtime.store.ModuleInst} {instIndex : Usize} {source : List Itasca.metadata.Element}
    (effect : DataStageEffect store instIndex inst after)
    (found : store.instances.val[instIndex.val]? = some inst)
    (nextFound : after.instances.val[instIndex.val]? = some next)
    (matching : ElementTypeMap store source inst.elems.val) : ElementTypeMap after source next.elems.val := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    simpa only [same] using matching
  | appended datas addresses data stored mapped =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    exact matching

end Itasca.Store

end

end

/-! ## ElementShapeLoop -/

section

open Itasca.Representation

/-! ## SegmentEffects -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

theorem GlobalStageEffect.segment_accounting {M : Type} {store after : runtime.store.Store M}
    {index : Usize} {inst : runtime.store.ModuleInst}
    (effect : GlobalStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (accounted : SegmentAccounting store) : SegmentAccounting after := by
  cases effect with
  | unchanged => exact accounted
  | appended globals addresses global globalValues addressValues shape room =>
    apply accounted.update_instance index inst {inst with globals := addresses} found rfl 0 0 <;> simp

theorem ElementStageEffect.segment_accounting {M : Type} {store after : runtime.store.Store M}
    {index : Usize} {inst : runtime.store.ModuleInst}
    (effect : ElementStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (accounted : SegmentAccounting store) : SegmentAccounting after := by
  cases effect with
  | unchanged => exact accounted
  | appended elements addresses element elementValues addressValues =>
    apply accounted.update_instance index inst {inst with elems := addresses} found rfl 1 0
    · simpa using congrArg List.length elementValues
    · simp
    · simpa using congrArg List.length addressValues
    · simp

theorem DataStageEffect.segment_accounting {M : Type} {store after : runtime.store.Store M}
    {index : Usize} {inst : runtime.store.ModuleInst}
    (effect : DataStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (accounted : SegmentAccounting store) : SegmentAccounting after := by
  cases effect with
  | unchanged => exact accounted
  | appended datas addresses data dataValues addressValues =>
    apply accounted.update_instance index inst {inst with datas := addresses} found rfl 0 1
    · simp
    · simpa using congrArg List.length dataValues
    · simp
    · simpa using congrArg List.length addressValues

end Itasca.Store

end

/-! ## InitializerMetadata -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- Constant/segment staging changes only value and segment maps. The exact
metadata used by retained function certificates remains unchanged. -/
structure InitializerFunctionMetadata {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (after : runtime.store.Store M) (next : runtime.store.ModuleInst) : Prop where
  identity : after.id = store.id
  functions : after.funcs = store.funcs
  signatures : after.types = store.types
  source : next.module = inst.module
  typeMap : next.types = inst.types
  functionMap : next.funcs = inst.funcs
  tables : after.tables = store.tables
  tableMap : next.tables = inst.tables
  memories : after.memories = store.memories
  memoryMap : next.memories = inst.memories
  instanceCount : after.instances.length = store.instances.length

theorem InitializerFunctionMetadata.refl {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) : InitializerFunctionMetadata store inst store inst := by
  constructor <;> rfl

theorem InitializerFunctionMetadata.trans {M : Type} {a b c : runtime.store.Store M}
    {i j k : runtime.store.ModuleInst} (first : InitializerFunctionMetadata a i b j)
    (second : InitializerFunctionMetadata b j c k) : InitializerFunctionMetadata a i c k := by
  exact ⟨second.identity.trans first.identity, second.functions.trans first.functions,
    second.signatures.trans first.signatures, second.source.trans first.source,
    second.typeMap.trans first.typeMap, second.functionMap.trans first.functionMap,
    second.tables.trans first.tables, second.tableMap.trans first.tableMap,
    second.memories.trans first.memories, second.memoryMap.trans first.memoryMap,
    second.instanceCount.trans first.instanceCount⟩

def InitializerFunctionMetadataAt {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (after : runtime.store.Store M) (index : Usize) : Prop :=
  ∃ next, after.instances.val[index.val]? = some next ∧ InitializerFunctionMetadata store inst after next

theorem InitializerFunctionMetadataAt.resolve {M : Type} {store after : runtime.store.Store M}
    {inst next : runtime.store.ModuleInst} {index : Usize}
    (metadata : InitializerFunctionMetadataAt store inst after index)
    (found : after.instances.val[index.val]? = some next) : InitializerFunctionMetadata store inst after next := by
  obtain ⟨actual, lookup, matching⟩ := metadata
  have same : actual = next := Option.some.inj (lookup.symm.trans found)
  exact same ▸ matching

theorem GlobalStageEffect.function_metadata {M : Type} {store after : runtime.store.Store M}
    {index : Usize} {inst next : runtime.store.ModuleInst}
    (effect : GlobalStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (nextFound : after.instances.val[index.val]? = some next) :
    InitializerFunctionMetadata store inst after next := by
  cases effect with
  | unchanged =>
    have same : inst = next := Option.some.inj (found.symm.trans nextFound)
    subst next
    exact .refl _ _
  | appended globals addresses global globalValues addressValues canonical room =>
    have bound : index.val < store.instances.val.length := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte,
      Option.some.injEq] at nextFound
    subst next
    constructor <;> try rfl
    simp [alloc.vec.Vec.length, alloc.vec.Vec.set_val_eq]

theorem ElementStageEffect.function_metadata {M : Type} {store after : runtime.store.Store M}
    {index : Usize} {inst next : runtime.store.ModuleInst}
    (effect : ElementStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (nextFound : after.instances.val[index.val]? = some next) :
    InitializerFunctionMetadata store inst after next := by
  cases effect with
  | unchanged =>
    have same : inst = next := Option.some.inj (found.symm.trans nextFound)
    subst next
    exact .refl _ _
  | appended elements addresses element elementValues addressValues =>
    have bound : index.val < store.instances.val.length := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte,
      Option.some.injEq] at nextFound
    subst next
    constructor <;> try rfl
    simp [alloc.vec.Vec.length, alloc.vec.Vec.set_val_eq]

theorem DataStageEffect.function_metadata {M : Type} {store after : runtime.store.Store M}
    {index : Usize} {inst next : runtime.store.ModuleInst}
    (effect : DataStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (nextFound : after.instances.val[index.val]? = some next) :
    InitializerFunctionMetadata store inst after next := by
  cases effect with
  | unchanged =>
    have same : inst = next := Option.some.inj (found.symm.trans nextFound)
    subst next
    exact .refl _ _
  | appended datas addresses data dataValues addressValues =>
    have bound : index.val < store.instances.val.length := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte,
      Option.some.injEq] at nextFound
    subst next
    constructor <;> try rfl
    simp [alloc.vec.Vec.length, alloc.vec.Vec.set_val_eq]

end Itasca.Store

end

/-! ## ElementShapeLoop -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

private theorem elem_value_type_eq (ty : Itasca.wasm_types.ElemType) :
    wasm_types.ElemType.value_type ty = .ok (elementValueType ty) := by cases ty <;> rfl

private theorem encode_push_shape {M : Type} (store : runtime.store.Store M)
    (values : alloc.vec.Vec U64) (value : runtime.Value) (ty : Itasca.wasm_types.ElemType)
    (typed : elementValueType ty = Representation.rawType value) (owned : ValueInStore store value)
    (previous : ∀ word ∈ values.val, ReferenceShape store ty word)
    (room : values.length < Usize.max) :
    (do let (lo, _) ← runtime.value.encode value
        let next ← alloc.vec.Vec.push values lo
        .ok (next, (core.result.Result.Ok () : core.result.Result Unit runtime.ExecError)))
      ⦃ out => out.1.length = values.length + 1 ∧ out.2 = .Ok () ∧
        ∀ word ∈ out.1.val, ReferenceShape store ty word ⦄ := by
  step with encode_reference_shape store value ty typed owned as ⟨lo, high, shaped⟩
  step as ⟨next, hnext⟩
  refine ⟨by simp [alloc.vec.Vec.length, hnext], ?_⟩
  intro word member
  simp only [hnext, List.mem_append, List.mem_singleton] at member
  rcases member with old | rfl
  · exact previous word old
  · exact shaped

theorem element_initializers_shape_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index length : Usize)
    (inst : runtime.store.ModuleInst) (segment : Itasca.metadata.Element)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (helem : inst.module.module.env.elements.val[index.val]? = some segment)
    (hlength : length.val = segment.init.length)
    (certificates : ElementInitializers store inst index segment)
    (bindings : InitializerBindings store inst)
    (values : alloc.vec.Vec U64) (j : Usize) (status : core.result.Result Unit runtime.ExecError)
    (hvalues : values.length ≤ j.val) (hj : j.val ≤ length.val)
    (shaped : ∀ word ∈ values.val, ReferenceShape store segment.elem word) :
    runtime.store.instantiate.Store.add_instance_element_loop memory hooks floats allocator store platform
      instIndex index length values j status ⦃ out =>
        out.1 = store ∧ out.2.1 = platform ∧ out.2.2.1.length ≤ length.val ∧
        ∀ word ∈ out.2.2.1.val, ReferenceShape store segment.elem word ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_element_loop
  apply loop.spec_decr_nat (fun p => length.val - p.2.2.2.1.val)
    (fun p => p.1 = store ∧ p.2.1 = platform ∧
      p.2.2.1.length ≤ p.2.2.2.1.val ∧ p.2.2.2.1.val ≤ length.val ∧
      ∀ word ∈ p.2.2.1.val, ReferenceShape store segment.elem word)
  · rintro ⟨current, host, vals, k, state⟩ ⟨hcurrent, hhost, hvals, hk, refs⟩
    dsimp only at hcurrent hhost hvals hk refs ⊢
    subst current host
    change vals.val.length ≤ k.val at hvals
    unfold runtime.store.instantiate.Store.add_instance_element_loop.body
    split
    · rename_i more
      have hmore : k.val < length.val := by scalar_tac
      cases state with
      | Err error =>
        simp [core.result.Result.is_ok]
        exact ⟨by omega, refs⟩
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        obtain ⟨functions, mapping, certificates⟩ := certificates
        obtain ⟨expr, function, code, words, hexpr, hfunction, hcode, compiled, resolved⟩ :=
          certificates k (by omega)
        step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
        subst found
        step with Interp.vec_index_given inst.module.element_initializers index functions mapping
          as ⟨found, hfound⟩
        subst found
        step with Interp.vec_index_given functions k function hfunction as ⟨found, hfound⟩
        subst found
        simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Env.impl.elements, bind_ok]
        step with Itasca.Representation.slice_index_given inst.module.module.env.elements.deref index segment
          (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
        subst found
        rw [elem_value_type_eq, bind_ok]
        step with eval_const_owned memory hooks floats allocator law store platform instIndex function
          inst code expr (elementValueType segment.elem) words hi hcode compiled resolved bindings
          as ⟨result, after, host', hs, hp, hvalue⟩
        subst after host'
        cases result with
        | Err error =>
          step as ⟨next, hnext⟩
          change vals.val.length ≤ next.val ∧ next.val ≤ length.val ∧
            (∀ word ∈ vals.val, ReferenceShape store segment.elem word) ∧ length.val - next.val < length.val - k.val
          exact ⟨by omega, by omega, refs, by omega⟩
        | Ok value =>
          obtain ⟨owned, typed⟩ := hvalue value rfl
          have room : vals.length < Usize.max := by scalar_tac
          apply WP.spec_bind (encode_push_shape store vals value segment.elem typed.symm owned refs room)
          rintro ⟨pushed, nextStatus⟩ ⟨hpush, hstatus, pushedRefs⟩
          step as ⟨next, hnext⟩
          refine ⟨?_, by omega, pushedRefs, by omega⟩
          rw [hpush]
          change vals.val.length + 1 ≤ next.val
          omega
    · have hstop : length.val ≤ k.val := by scalar_tac
      simp only [WP.spec_ok]
      simp only [true_and]
      change vals.val.length ≤ length.val ∧ ∀ word ∈ vals.val, ReferenceShape store segment.elem word
      exact ⟨by omega, refs⟩
  · exact ⟨rfl, rfl, hvalues, hj, shaped⟩

end Itasca.Store

end

end

/-! ## SegmentSourceStaging -/

section

open Itasca.Representation

/-!
# Source segment staging

Element content and source-value loops compose with global/data metadata and segment
bounds. Initializer certificates retain ordering and connect staged concrete objects to
source segments.
-/

/-! ## ElementContentEffect -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- Exact element staging retains the source reference type in the newly
allocated segment and distinguishes a normal refusal from successful append. -/
inductive ElementContentEffect {M : Type} (store : runtime.store.Store M)
    (instIndex : Usize) (inst : runtime.store.ModuleInst) (source : Itasca.metadata.Element) :
    core.result.Result Unit runtime.ExecError → runtime.store.Store M → Prop where
  | failed (error : runtime.ExecError) : ElementContentEffect store instIndex inst source (.Err error) store
  | appended (elements : alloc.vec.Vec runtime.store.ElemInst) (addresses : alloc.vec.Vec Usize)
      (values : alloc.vec.Vec U64)
      (elementValues : elements.val = store.elems.val ++ [{ty := source.elem, refs := values}])
      (addressValues : addresses.val = inst.elems.val ++ [store.elems.len])
      (canonical : ∀ word ∈ values.val, ReferenceShape store source.elem word) :
      ElementContentEffect store instIndex inst source (.Ok ())
        {store with elems := elements, instances := store.instances.set instIndex {inst with elems := addresses}}

theorem ElementContentEffect.typed {M : Type} {store after : runtime.store.Store M}
    {instIndex inst source status} (typed : ElementContentEffect store instIndex inst source status after) :
    ElementTypedEffect store instIndex inst source status after := by
  cases typed with
  | failed error => exact .failed error
  | appended elements addresses values stored mapped canonical => exact .appended elements addresses values stored mapped

def ElementContents {M : Type} (store : runtime.store.Store M) : Prop :=
  ∀ element ∈ store.elems.val, ∀ word ∈ element.refs.val, ReferenceShape store element.ty word

theorem ElementContentEffect.contents {M : Type} {store after : runtime.store.Store M}
    {instIndex inst source status} (effect : ElementContentEffect store instIndex inst source status after)
    (before : ElementContents store) : ElementContents after := by
  cases effect with
  | failed error => exact before
  | appended elements addresses values stored mapped canonical =>
    intro element member word contained
    simp only [stored, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · simpa only [ReferenceShape] using before element old word contained
    · simpa only [ReferenceShape] using canonical word contained

theorem add_instance_element_content_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.ModuleInst) (segment : Itasca.metadata.Element)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (helem : inst.module.module.env.elements.val[index.val]? = some segment)
    (certificates : ElementInitializers store inst index segment)
    (bindings : InitializerBindings store inst)
    (room : store.elems.length < Usize.max) (mapRoom : inst.elems.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_element memory hooks floats allocator store platform instIndex index
      ⦃ out => ElementContentEffect store instIndex inst segment out.1 out.2.1 ∧ out.2.2 = platform ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_element
  step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Env.impl.elements, bind_ok]
  step with Itasca.Representation.slice_index_given inst.module.module.env.elements.deref index segment
    (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
  subst found
  obtain ⟨reserved, hreserve⟩ := reserve_wrapper_eq allocator law (alloc.vec.Vec.new U64) segment.init.len
  rw [hreserve]
  cases reserved with
  | false =>
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementContentEffect.failed (store := store) (instIndex := instIndex) (inst := inst) (source := segment) (.Exhausted .Allocation))
  | true =>
    simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with element_initializers_shape_loop memory hooks floats allocator law store platform instIndex index
      segment.init.len inst segment hi helem (by simp) certificates bindings
      (alloc.vec.Vec.new U64) 0#usize (.Ok ()) (by simp) (by scalar_tac) (by simp)
      as ⟨after, host, values, status, hs, hp, hvalues, refs⟩
    subst after host
    cases status with
    | Err error =>
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementContentEffect.failed (store := store) (instIndex := instIndex) (inst := inst) (source := segment) error)
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨reserved, hreserve⟩ := reserve_wrapper_eq allocator law store.elems 1#usize
      rw [hreserve]
      cases reserved with
      | false =>
        simpa [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementContentEffect.failed (store := store) (instIndex := instIndex) (inst := inst) (source := segment) (.Exhausted .Allocation))
      | true =>
        simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
        subst found
        step with Itasca.Representation.slice_index_given inst.module.module.env.elements.deref index segment
          (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
        subst found
        step as ⟨elements, helements⟩
        have instanceBound : instIndex.val < store.instances.length :=
          (List.getElem?_eq_some_iff.mp hi).1
        step as ⟨old, back, hold, hback⟩
        have old_eq : old = inst := by
          have hread := List.getElem?_eq_getElem instanceBound
          rw [hi] at hread
          exact hold.trans (Option.some.inj hread).symm
        subst old
        step as ⟨addresses, haddresses⟩
        have instanceRead : store.instances.val[instIndex.val] = inst :=
          Option.some.inj ((List.getElem?_eq_getElem instanceBound).symm.trans hi)
        have effect := ElementContentEffect.appended (store := store) (instIndex := instIndex) (inst := inst) (source := segment)
          elements addresses values helements
          (by simpa only [instanceRead] using haddresses) refs
        simpa [hback, instanceRead] using And.intro effect (rfl : platform = platform)

end Itasca.Store

end

/-! ## SegmentGlobalMetadata -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

theorem ElementStageEffect.globals {M : Type} {store after : runtime.store.Store M}
    {index inst} (effect : ElementStageEffect store index inst after) : after.globals = store.globals := by
  cases effect <;> rfl

theorem ElementStageEffect.global_map {M : Type} {store after : runtime.store.Store M}
    {index inst next} (effect : ElementStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (nextFound : after.instances.val[index.val]? = some next) : next.globals = inst.globals := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    subst next
    rfl
  | appended elements addresses element stored mapped =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    rfl

theorem DataStageEffect.globals {M : Type} {store after : runtime.store.Store M}
    {index inst} (effect : DataStageEffect store index inst after) : after.globals = store.globals := by
  cases effect <;> rfl

theorem DataStageEffect.global_map {M : Type} {store after : runtime.store.Store M}
    {index inst next} (effect : DataStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (nextFound : after.instances.val[index.val]? = some next) : next.globals = inst.globals := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    subst next
    rfl
  | appended datas addresses data stored mapped =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    rfl

end Itasca.Store

end

/-! ## DataValueMetadata -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

theorem DataStageEffect.elements {M : Type} {store after : runtime.store.Store M}
    {index inst} (effect : DataStageEffect store index inst after) : after.elems = store.elems := by
  cases effect <;> rfl

theorem DataStageEffect.element_map {M : Type} {store after : runtime.store.Store M}
    {index inst next} (effect : DataStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (nextFound : after.instances.val[index.val]? = some next) : next.elems = inst.elems := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    subst next
    rfl
  | appended datas addresses data stored mapped =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    rfl
end Itasca.Store

end

/-! ## SegmentBoundsEffects -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

theorem SegmentBounds.same {M : Type} {before after : runtime.store.Store M}
    (bounded : SegmentBounds before) (elements : after.elems = before.elems) (datas : after.datas = before.datas) :
    SegmentBounds after := by
  constructor
  · simpa [elements] using bounded.elements
  · simpa [datas] using bounded.data

/-- Data staging copies the accepted source payload exactly, hence cannot grow
it beyond its binary vector count. Allocation refusal leaves all bounds intact. -/
theorem add_instance_data_bounds {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (instIndex index : Usize) (inst : runtime.store.ModuleInst)
    (found : store.instances.val[instIndex.val]? = some inst)
    (bound : index.val < inst.module.module.tail.data.val.length)
    (room : store.datas.length < Usize.max) (mapRoom : inst.datas.length < Usize.max)
    (sourceBound : ∀ data ∈ inst.module.module.tail.data.val, data.init.length < 2^32)
    (bounded : SegmentBounds store) :
    runtime.store.instantiate.Store.add_instance_data memory allocator store instIndex index
      ⦃ out => SegmentBounds out.2 ⦄ := by
  have instanceBound : instIndex.val < store.instances.length := (List.getElem?_eq_some_iff.mp found).1
  have instanceRead : store.instances.val[instIndex.val] = inst := (List.getElem?_eq_some_iff.mp found).2
  apply WP.spec_mono (add_instance_data_effect memory allocator law store instIndex index instanceBound
    (by simpa only [instanceRead] using bound) room (by simpa only [instanceRead] using mapRoom))
  intro out effect
  rcases effect with ⟨error, rfl⟩ | ⟨bytes, datas, addresses, copied, appended, mapped, rfl⟩
  · exact bounded
  · constructor
    · exact bounded.elements
    · intro data member
      simp only [appended, List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · exact bounded.data data old
      · have source := sourceBound _ (List.getElem_mem bound)
        simpa only [alloc.vec.Vec.length, copied, instanceRead] using source
end Itasca.Store

end

/-! ## ElementCompleteLoop -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

theorem element_complete_staging_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (platform : P) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : Compiler.InitializerMappings inst.module)
    (valid : ∀ segment ∈ inst.module.module.env.elements.val,
      Itasca.Module.Segments.elementValid inst.module.module.env segment)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (startBound : start.val ≤ inst.module.module.env.elements.val.length)
    (storeCapacity : store.elems.length + (inst.module.module.env.elements.val.length - start.val) ≤ Usize.max)
    (mapCapacity : inst.elems.length + (inst.module.module.env.elements.val.length - start.val) ≤ Usize.max)
    (matching : status = .Ok () → ElementTypeMap store (inst.module.module.env.elements.val.take start.val) inst.elems.val)
    (contents : ElementContents store) :
    runtime.store.instantiate.Store.prepare_instance_loop8 memory hooks floats allocator store platform status start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeParts after platform finalStatus ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ ElementContents after ∧ after.globals = store.globals ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ ∃ next,
          after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧ next.globals = inst.globals ∧
          InitializerBindings after next ∧ InitializerImports after next ∧ InitializerSegmentBindings after next ∧
          after.datas = store.datas ∧ next.datas = inst.datas ∧
          (finalStatus = .Ok () → ElementTypeMap after inst.module.module.env.elements.val next.elems.val) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop8
  apply loop.spec_decr_nat (fun state => inst.module.module.env.elements.val.length - state.2.2.2.val)
    (fun state => state.2.1 = platform ∧ StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ ElementContents state.1 ∧ state.1.globals = store.globals ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.2.val ≤ inst.module.module.env.elements.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧ currentInst.globals = inst.globals ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.elems.length + (inst.module.module.env.elements.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.elems.length + (inst.module.module.env.elements.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.datas = store.datas ∧ currentInst.datas = inst.datas ∧
        (state.2.2.1 = .Ok () → ElementTypeMap state.1 (inst.module.module.env.elements.val.take state.2.2.2.val) currentInst.elems.val))
  · rintro ⟨current, host, result, index⟩ ⟨hhost, hstaged, hobjects, hcontents, hglobals, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, hglobalMap, hbindings, himports, hsegments, hcapacity, hstoreCapacity, hdatas, hmapData, htyped⟩
    dsimp only at hhost hstaged hobjects hcontents hglobals haccounted hmetadata hindex hfound hsource hglobalMap hbindings himports hsegments hcapacity hstoreCapacity hdatas hmapData htyped ⊢
    subst host
    unfold runtime.store.instantiate.Store.prepare_instance_loop8.body
    step with Interp.vec_index_given current.instances instIndex currentInst hfound as ⟨actual, hactual⟩
    subst actual
    simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Env.impl.elements, bind_ok, hsource]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.env.elements.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, .Err error, rfl, hstaged, hobjects, hcontents, hglobals, haccounted, hmetadata,
          currentInst, hfound, hsource, hglobalMap, hbindings, himports, hsegments, hdatas, hmapData, by simp⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        let segment := inst.module.module.env.elements.val[index.val]
        have hsegment : currentInst.module.module.env.elements.val[index.val]? = some segment := by
          rw [hsource]
          exact List.getElem?_eq_getElem hmore
        have hvalid : Itasca.Module.Segments.elementValid currentInst.module.module.env segment := by
          rw [hsource]
          exact valid segment (List.mem_of_getElem? (List.getElem?_eq_getElem hmore))
        have certificates := element_initializer_certificates current currentInst index segment
          (by simpa [hsource] using compiled) hsegment hvalid hbindings himports
        have room : current.elems.length < Usize.max := by omega
        have mapRoom : currentInst.elems.length < Usize.max := by omega
        step with add_instance_element_content_effect memory hooks floats allocator law current platform instIndex index
          currentInst segment hfound hsegment certificates hbindings room mapRoom
          as ⟨state, after, host', contentEffect, hhost'⟩
        subst host'
        have typedEffect := contentEffect.typed
        have effect := typedEffect.effect
        obtain ⟨nextInst, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextSize, nextStoreSize, nextData⟩ :=
          effect.context hfound hbindings himports hsegments
        have nextMetadata : InitializerFunctionMetadataAt store inst after instIndex :=
          ⟨nextInst, nextFound, (hmetadata.resolve hfound).trans (effect.function_metadata hfound nextFound)⟩
        have nextStaged := effect.staged hstaged fresh
        have nextObjects : objectCount after ≤ Usize.max := by simpa only [effect.object_count] using hobjects
        have counterCapacity := inst.module.module.env.elements.property
        step as ⟨next, hnext⟩
        refine ⟨nextStaged, nextObjects, contentEffect.contents hcontents, effect.globals.trans hglobals, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, (effect.global_map hfound nextFound).trans hglobalMap, nextBindings, nextImports, nextSegments, ?_,
          ?_, effect.data.trans hdatas, nextData.trans hmapData, ?_⟩, ?_⟩
        · omega
        · omega
        · omega
        · intro success
          have typed := typedEffect.type_map (List.getElem?_eq_some_iff.mp hfound).1 nextFound (htyped rfl) success
          simpa only [hnext, List.take_succ_eq_append_getElem hmore] using typed
        · omega
    · rename_i stopped
      have atEnd : index.val = inst.module.module.env.elements.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      exact ⟨current, result, rfl, hstaged, hobjects, hcontents, hglobals, haccounted, hmetadata,
        currentInst, hfound, hsource, hglobalMap, hbindings, himports, hsegments, hdatas, hmapData, fun success => by simpa only [atEnd, List.take_length] using htyped success⟩
  · exact ⟨rfl, staged, objectBound, contents, rfl, (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, rfl, bindings, imports, segments, mapCapacity, storeCapacity, rfl, rfl, matching⟩

end Itasca.Store

end

/-! ## InitializerMetadataCertificates -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std
open Itasca.Module.Environment

theorem InitializerFunctionMetadata.type_entries {M : Type}
    {store after : runtime.store.Store M} {inst next : runtime.store.ModuleInst}
    (metadata : InitializerFunctionMetadata store inst after next)
    {source : List Itasca.wasm_types.FuncType} (entries : TypeEntries store source inst.types.val) :
    TypeEntries after source next.types.val := by
  simpa only [TypeEntries, metadata.signatures, metadata.typeMap] using entries

theorem InitializerFunctionMetadata.function_table {M : Type}
    {store after : runtime.store.Store M} {inst next : runtime.store.ModuleInst}
    (metadata : InitializerFunctionMetadata store inst after next)
    {types : List functype} (table : Representation.FunctionTable store inst types) :
    Representation.FunctionTable after next types := by
  simpa only [Representation.FunctionTable, metadata.identity, metadata.functions,
    metadata.signatures, metadata.functionMap] using table

theorem InitializerFunctionMetadata.staged_functions {M : Type}
    {before store after : runtime.store.Store M} {inst next : runtime.store.ModuleInst}
    (metadata : InitializerFunctionMetadata store inst after next) {index : Usize}
    {types : List Itasca.wasm_types.FuncType} (staged : StagedFunctionSignatures before store index types) :
    StagedFunctionSignatures before after index types := by
  simpa only [StagedFunctionSignatures, metadata.functions, metadata.signatures] using staged

end Itasca.Store

end

/-! ## ElementSourceLoop -/

section

/-!
Source values of allocated element segments. Constant evaluation and encoded pushes establish the source-element initializer loop relation.
-/

/-! ## Element Source Values -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

def ElementSourceValues (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (ty : Itasca.wasm_types.ElemType) (expressions : List Itasca.wasm_types.ConstExpr) (words : List U64) : Prop :=
  List.Forall₂ (fun expr word => Eval_expr ⟨sourceStore, ⟨[], sourceInstance⟩⟩
    (Itasca.Module.Constants.expression expr) ⟨sourceStore, ⟨[], sourceInstance⟩⟩
    [refVal (decodeRef ty word)]) expressions words

theorem eval_const_source {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (words : List U64)
    (found : store.instances.val[instIndex.val]? = some inst)
    (codeFound : inst.module.functions.val[function.val]? = some code)
    (compiled : Compiler.InitializerCode code expr ty)
    (resolved : Interp.InitializerResolution store inst expr ty words)
    (bindings : InitializerBindings store inst)
    (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (storeWf : wf_store sourceStore) (frameWf : wf_frame ⟨[], sourceInstance⟩)
    (context : InitializerSourceContext sourceStore sourceInstance store inst)
    (valid : Itasca.Module.Constants.Valid inst.module.module.env expr ty) :
    runtime.interp.eval_const memory hooks floats allocator store platform instIndex function ty
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧ ∀ value, out.1 = .Ok value →
        ValueInStore store value ∧ Representation.rawType value = ty ∧
        Eval_expr ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (Itasca.Module.Constants.expression expr)
          ⟨sourceStore, ⟨[], sourceInstance⟩⟩ [Representation.sourceValue value] ⦄ := by
  have exactValue := eval_const_effect memory hooks floats allocator law store platform instIndex function
    inst code expr ty words found codeFound compiled resolved (initializer_reference_bound resolved bindings)
  obtain ⟨result, run, owned⟩ := WP.spec_imp_exists
    (eval_const_owned memory hooks floats allocator law store platform instIndex function
      inst code expr ty words found codeFound compiled resolved bindings)
  rw [run] at exactValue ⊢
  simp only [WP.spec_ok] at exactValue ⊢
  refine ⟨owned.1, owned.2.1, ?_⟩
  intro value success
  refine ⟨(owned.2.2 value success).1, (owned.2.2 value success).2, ?_⟩
  rw [(exactValue.2.2 value success).2]
  exact context.expression valid resolved storeWf frameWf

theorem encode_push_source {M : Type} (store : runtime.store.Store M)
    (values : alloc.vec.Vec U64) (value : runtime.Value) (ty : Itasca.wasm_types.ElemType)
    (typed : elementValueType ty = Representation.rawType value) (owned : ValueInStore store value)
    (previous : ∀ word ∈ values.val, ReferenceShape store ty word)
    (room : values.length < Usize.max)
    (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (expressions : List Itasca.wasm_types.ConstExpr) (expr : Itasca.wasm_types.ConstExpr)
    (matched : ElementSourceValues sourceStore sourceInstance ty expressions values.val)
    (evaluated : Eval_expr ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (Itasca.Module.Constants.expression expr)
      ⟨sourceStore, ⟨[], sourceInstance⟩⟩ [Representation.sourceValue value]) :
    (do let (lo, _) ← runtime.value.encode value
        let next ← alloc.vec.Vec.push values lo
        .ok (next, (core.result.Result.Ok () : core.result.Result Unit runtime.ExecError)))
      ⦃ out => out.1.length = values.length + 1 ∧ out.2 = .Ok () ∧
        (∀ word ∈ out.1.val, ReferenceShape store ty word) ∧
        ElementSourceValues sourceStore sourceInstance ty (expressions ++ [expr]) out.1.val ⦄ := by
  obtain ⟨pair, encoded, canonical⟩ := WP.spec_imp_exists (encode_reference_shape store value ty typed owned)
  rw [encoded, bind_ok]
  rcases pair with ⟨lo, hi⟩
  have decoded := decode_encoded_value store value owned (lo, hi) encoded
  rw [← typed] at decoded
  have exactRef : refVal (decodeRef ty lo) = Representation.sourceValue value := by
    cases ty <;> simpa only [elementValueType, decodeWords] using decoded
  step as ⟨next, stored⟩
  refine ⟨by simp [stored], ?_, ?_⟩
  · intro word member
    simp only [stored, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact previous word old
    · exact canonical
  · unfold ElementSourceValues at matched ⊢
    rw [stored]
    exact List.rel_append matched (.cons (by simpa only [exactRef] using evaluated) .nil)
end Itasca.Store

end

/-! ## Element Source Loop -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

theorem element_initializers_source_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index length : Usize)
    (inst : runtime.store.ModuleInst) (segment : Itasca.metadata.Element)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (helem : inst.module.module.env.elements.val[index.val]? = some segment)
    (hlength : length.val = segment.init.length)
    (certificates : ElementInitializers store inst index segment)
    (bindings : InitializerBindings store inst)
    (values : alloc.vec.Vec U64) (j : Usize) (status : core.result.Result Unit runtime.ExecError)
    (hvalues : values.length ≤ j.val) (hj : j.val ≤ length.val)
    (shaped : ∀ word ∈ values.val, ReferenceShape store segment.elem word)
    (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (storeWf : wf_store sourceStore) (frameWf : wf_frame ⟨[], sourceInstance⟩)
    (context : InitializerSourceContext sourceStore sourceInstance store inst)
    (valid : ∀ expr ∈ segment.init.val,
      Itasca.Module.Constants.Valid inst.module.module.env expr (elementValueType segment.elem))
    (matched : status = .Ok () → ElementSourceValues sourceStore sourceInstance segment.elem
      (segment.init.val.take j.val) values.val) :
    runtime.store.instantiate.Store.add_instance_element_loop memory hooks floats allocator store platform
      instIndex index length values j status ⦃ out =>
        out.1 = store ∧ out.2.1 = platform ∧ out.2.2.1.length ≤ length.val ∧
        (∀ word ∈ out.2.2.1.val, ReferenceShape store segment.elem word) ∧
        (out.2.2.2 = .Ok () → ElementSourceValues sourceStore sourceInstance segment.elem segment.init.val out.2.2.1.val) ⦄ := by
  have segmentLength : length.val = segment.init.val.length := hlength
  unfold runtime.store.instantiate.Store.add_instance_element_loop
  apply loop.spec_decr_nat (fun p => length.val - p.2.2.2.1.val)
    (fun p => p.1 = store ∧ p.2.1 = platform ∧
      p.2.2.1.length ≤ p.2.2.2.1.val ∧ p.2.2.2.1.val ≤ length.val ∧
      (∀ word ∈ p.2.2.1.val, ReferenceShape store segment.elem word) ∧
      (p.2.2.2.2 = .Ok () → ElementSourceValues sourceStore sourceInstance segment.elem
        (segment.init.val.take p.2.2.2.1.val) p.2.2.1.val))
  · rintro ⟨current, host, vals, k, state⟩ ⟨hcurrent, hhost, hvals, hk, refs, currentMatched⟩
    dsimp only at hcurrent hhost hvals hk refs currentMatched ⊢
    subst current host
    change vals.val.length ≤ k.val at hvals
    unfold runtime.store.instantiate.Store.add_instance_element_loop.body
    split
    · rename_i more
      have hmore : k.val < length.val := by scalar_tac
      cases state with
      | Err error =>
        simp [core.result.Result.is_ok]
        exact ⟨by omega, refs⟩
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        obtain ⟨functions, mapping, certificates⟩ := certificates
        obtain ⟨expr, function, code, words, hexpr, hfunction, hcode, compiled, resolved⟩ :=
          certificates k (by omega)
        step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
        subst found
        step with Interp.vec_index_given inst.module.element_initializers index functions mapping
          as ⟨found, hfound⟩
        subst found
        step with Interp.vec_index_given functions k function hfunction as ⟨found, hfound⟩
        subst found
        simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Env.impl.elements, bind_ok]
        step with Itasca.Representation.slice_index_given inst.module.module.env.elements.deref index segment
          (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
        subst found
        rw [elem_value_type_eq, bind_ok]
        step with eval_const_source memory hooks floats allocator law store platform instIndex function
          inst code expr (elementValueType segment.elem) words hi hcode compiled resolved bindings
          sourceStore sourceInstance storeWf frameWf context
          (valid expr (List.mem_of_getElem? hexpr))
          as ⟨result, after, host', hs, hp, hvalue⟩
        subst after host'
        cases result with
        | Err error =>
          step as ⟨next, hnext⟩
          change vals.val.length ≤ next.val ∧ next.val ≤ length.val ∧
            (∀ word ∈ vals.val, ReferenceShape store segment.elem word) ∧
            ((core.result.Result.Err error : core.result.Result Unit runtime.ExecError) = .Ok () → _ ) ∧
            length.val - next.val < length.val - k.val
          exact ⟨by omega, by omega, refs, by simp, by omega⟩
        | Ok value =>
          obtain ⟨owned, typed, evaluated⟩ := hvalue value rfl
          have room : vals.length < Usize.max := by scalar_tac
          apply WP.spec_bind (encode_push_source store vals value segment.elem typed.symm owned refs room
            sourceStore sourceInstance (segment.init.val.take k.val) expr (currentMatched rfl) evaluated)
          rintro ⟨pushed, nextStatus⟩ ⟨hpush, hstatus, pushedRefs, pushedMatched⟩
          step as ⟨next, hnext⟩
          refine ⟨?_, by omega, pushedRefs, ?_, by omega⟩
          · rw [hpush]
            change vals.val.length + 1 ≤ next.val
            omega
          · intro _
            rw [hnext, List.take_succ_eq_append_getElem (by omega)]
            have exprEq := (List.getElem?_eq_some_iff.mp hexpr).2
            simpa only [exprEq] using pushedMatched
    · have hstop : length.val ≤ k.val := by scalar_tac
      simp only [WP.spec_ok]
      simp only [true_and]
      change vals.val.length ≤ length.val ∧ (∀ word ∈ vals.val, ReferenceShape store segment.elem word) ∧
        (state = .Ok () → ElementSourceValues sourceStore sourceInstance segment.elem segment.init.val vals.val)
      refine ⟨by omega, refs, ?_⟩
      intro success
      have atEnd : k.val = segment.init.val.length := by omega
      simpa only [atEnd, List.take_length] using currentMatched success
  · exact ⟨rfl, rfl, hvalues, hj, shaped, matched⟩

end Itasca.Store

end

end

/-! ## ElementValues -/

section

/-!
Allocated element values and their decoded source-segment relation. Typed content and loop shape remain lower certificates used independently by initialization.
-/

/-! ## Element Value Effect -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

inductive ElementValueEffect {M : Type} (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (store : runtime.store.Store M) (instIndex : Usize) (inst : runtime.store.ModuleInst)
    (source : Itasca.metadata.Element) : core.result.Result Unit runtime.ExecError → runtime.store.Store M → Prop where
  | failed (error : runtime.ExecError) : ElementValueEffect sourceStore sourceInstance store instIndex inst source (.Err error) store
  | appended (elements : alloc.vec.Vec runtime.store.ElemInst) (addresses : alloc.vec.Vec Usize)
      (values : alloc.vec.Vec U64)
      (elementValues : elements.val = store.elems.val ++ [{ty := source.elem, refs := values}])
      (addressValues : addresses.val = inst.elems.val ++ [store.elems.len])
      (canonical : ∀ word ∈ values.val, ReferenceShape store source.elem word)
      (evaluated : ElementSourceValues sourceStore sourceInstance source.elem source.init.val values.val) :
      ElementValueEffect sourceStore sourceInstance store instIndex inst source (.Ok ())
        {store with elems := elements, instances := store.instances.set instIndex {inst with elems := addresses}}

theorem ElementValueEffect.content {M : Type} {sourceStore sourceInstance}
    {store after : runtime.store.Store M} {instIndex inst source status}
    (effect : ElementValueEffect sourceStore sourceInstance store instIndex inst source status after) :
    ElementContentEffect store instIndex inst source status after := by
  cases effect with
  | failed error => exact .failed error
  | appended elements addresses values stored mapped canonical evaluated =>
    exact .appended elements addresses values stored mapped canonical

theorem add_instance_element_value_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.ModuleInst) (segment : Itasca.metadata.Element)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (helem : inst.module.module.env.elements.val[index.val]? = some segment)
    (certificates : ElementInitializers store inst index segment)
    (bindings : InitializerBindings store inst)
    (room : store.elems.length < Usize.max) (mapRoom : inst.elems.length < Usize.max)
    (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (storeWf : wf_store sourceStore) (frameWf : wf_frame ⟨[], sourceInstance⟩)
    (context : InitializerSourceContext sourceStore sourceInstance store inst)
    (valid : ∀ expr ∈ segment.init.val,
      Itasca.Module.Constants.Valid inst.module.module.env expr (elementValueType segment.elem)) :
    runtime.store.instantiate.Store.add_instance_element memory hooks floats allocator store platform instIndex index
      ⦃ out => ElementValueEffect sourceStore sourceInstance store instIndex inst segment out.1 out.2.1 ∧ out.2.2 = platform ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_element
  step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Env.impl.elements, bind_ok]
  step with Itasca.Representation.slice_index_given inst.module.module.env.elements.deref index segment
    (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
  subst found
  obtain ⟨reserved, hreserve⟩ := reserve_wrapper_eq allocator law (alloc.vec.Vec.new U64) segment.init.len
  rw [hreserve]
  cases reserved with
  | false =>
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementValueEffect.failed (sourceStore := sourceStore) (sourceInstance := sourceInstance) (store := store) (instIndex := instIndex) (inst := inst) (source := segment) (.Exhausted .Allocation))
  | true =>
    simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with element_initializers_source_loop memory hooks floats allocator law store platform instIndex index
      segment.init.len inst segment hi helem (by simp) certificates bindings
      (alloc.vec.Vec.new U64) 0#usize (.Ok ()) (by simp) (by scalar_tac) (by simp)
      sourceStore sourceInstance storeWf frameWf context valid (by simp [ElementSourceValues])
      as ⟨after, host, values, status, hs, hp, hvalues, refs, evaluated⟩
    subst after host
    cases status with
    | Err error =>
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementValueEffect.failed (sourceStore := sourceStore) (sourceInstance := sourceInstance) (store := store) (instIndex := instIndex) (inst := inst) (source := segment) error)
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨reserved, hreserve⟩ := reserve_wrapper_eq allocator law store.elems 1#usize
      rw [hreserve]
      cases reserved with
      | false =>
        simpa [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementValueEffect.failed (sourceStore := sourceStore) (sourceInstance := sourceInstance) (store := store) (instIndex := instIndex) (inst := inst) (source := segment) (.Exhausted .Allocation))
      | true =>
        simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
        subst found
        step with Itasca.Representation.slice_index_given inst.module.module.env.elements.deref index segment
          (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
        subst found
        step as ⟨elements, helements⟩
        have instanceBound : instIndex.val < store.instances.length :=
          (List.getElem?_eq_some_iff.mp hi).1
        step as ⟨old, back, hold, hback⟩
        have old_eq : old = inst := by
          have hread := List.getElem?_eq_getElem instanceBound
          rw [hi] at hread
          exact hold.trans (Option.some.inj hread).symm
        subst old
        step as ⟨addresses, haddresses⟩
        have instanceRead : store.instances.val[instIndex.val] = inst :=
          Option.some.inj ((List.getElem?_eq_getElem instanceBound).symm.trans hi)
        have effect := ElementValueEffect.appended (sourceStore := sourceStore) (sourceInstance := sourceInstance) (store := store) (instIndex := instIndex) (inst := inst) (source := segment)
          elements addresses values helements
          (by simpa only [instanceRead] using haddresses) refs (evaluated rfl)
        simpa [hback, instanceRead] using And.intro effect (rfl : platform = platform)

end Itasca.Store

end

/-! ## Element Value Source -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

def ElementSourceSegments (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (source : List Itasca.metadata.Element) (values : List runtime.store.ElemInst) : Prop :=
  List.Forall₂ (fun original actual => actual.ty = original.elem ∧
    ElementSourceValues sourceStore sourceInstance original.elem original.init.val actual.refs.val) source values

theorem ElementStageEffect.source_context {M : Type} {store after : runtime.store.Store M}
    {instIndex inst next sourceStore sourceInstance}
    (effect : ElementStageEffect store instIndex inst after)
    (found : store.instances.val[instIndex.val]? = some inst)
    (nextFound : after.instances.val[instIndex.val]? = some next)
    (context : InitializerSourceContext sourceStore sourceInstance store inst) :
    InitializerSourceContext sourceStore sourceInstance after next := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    subst next
    exact context
  | appended elements addresses element stored mapped =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    exact ⟨context.functions, context.globals⟩

theorem ElementValueEffect.source_values {M : Type} {store after : runtime.store.Store M}
    {instIndex inst sourceStore sourceInstance status}
    {original : Itasca.metadata.Element}
    (effect : ElementValueEffect sourceStore sourceInstance store instIndex inst original status after)
    {sources : List Itasca.metadata.Element} {base produced : List runtime.store.ElemInst}
    (stored : store.elems.val = base ++ produced)
    (previous : ElementSourceSegments sourceStore sourceInstance sources produced)
    (success : status = .Ok ()) :
    ∃ values, after.elems.val = base ++ values ∧
      ElementSourceSegments sourceStore sourceInstance (sources ++ [original]) values := by
  cases effect with
  | failed error => simp at success
  | appended elements addresses values entries mapped canonical evaluated =>
    refine ⟨produced ++ [{ty := original.elem, refs := values}], ?_, ?_⟩
    · simpa only [stored, List.append_assoc] using entries
    · exact List.rel_append previous (.cons ⟨rfl, evaluated⟩ .nil)
end Itasca.Store

end

end

/-! ## ElementSourceStaging -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

theorem element_source_staging_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (platform : P) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : Compiler.InitializerMappings inst.module)
    (valid : ∀ segment ∈ inst.module.module.env.elements.val,
      Itasca.Module.Segments.elementValid inst.module.module.env segment)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (startBound : start.val ≤ inst.module.module.env.elements.val.length)
    (storeCapacity : store.elems.length + (inst.module.module.env.elements.val.length - start.val) ≤ Usize.max)
    (mapCapacity : inst.elems.length + (inst.module.module.env.elements.val.length - start.val) ≤ Usize.max)
    (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (storeWf : wf_store sourceStore) (frameWf : wf_frame ⟨[], sourceInstance⟩)
    (sourceContext : InitializerSourceContext sourceStore sourceInstance store inst)
    (baseElements : List runtime.store.ElemInst)
    (matching : status = .Ok () → ∃ produced, store.elems.val = baseElements ++ produced ∧
      ElementSourceSegments sourceStore sourceInstance
        (inst.module.module.env.elements.val.take start.val) produced) :
    runtime.store.instantiate.Store.prepare_instance_loop8 memory hooks floats allocator store platform status start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeParts after platform finalStatus ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ ∃ next,
          after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
          InitializerBindings after next ∧ InitializerImports after next ∧ InitializerSegmentBindings after next ∧
          after.datas = store.datas ∧ next.datas = inst.datas ∧ after.globals = store.globals ∧ next.globals = inst.globals ∧
          InitializerSourceContext sourceStore sourceInstance after next ∧
          (finalStatus = .Ok () → ∃ produced, after.elems.val = baseElements ++ produced ∧
            ElementSourceSegments sourceStore sourceInstance inst.module.module.env.elements.val produced) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop8
  apply loop.spec_decr_nat (fun state => inst.module.module.env.elements.val.length - state.2.2.2.val)
    (fun state => state.2.1 = platform ∧ StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.2.val ≤ inst.module.module.env.elements.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.elems.length + (inst.module.module.env.elements.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.elems.length + (inst.module.module.env.elements.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.datas = store.datas ∧ currentInst.datas = inst.datas ∧ state.1.globals = store.globals ∧ currentInst.globals = inst.globals ∧
        InitializerSourceContext sourceStore sourceInstance state.1 currentInst ∧
        (state.2.2.1 = .Ok () → ∃ produced, state.1.elems.val = baseElements ++ produced ∧
          ElementSourceSegments sourceStore sourceInstance
            (inst.module.module.env.elements.val.take state.2.2.2.val) produced))
  · rintro ⟨current, host, result, index⟩ ⟨hhost, hstaged, hobjects, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, hbindings, himports, hsegments, hcapacity, hstoreCapacity, hdatas, hmapData, hglobals, hglobalMap, hcontext, hmatching⟩
    dsimp only at hhost hstaged hobjects haccounted hmetadata hindex hfound hsource hbindings himports hsegments hcapacity hstoreCapacity hdatas hmapData hglobals hglobalMap hcontext hmatching ⊢
    subst host
    unfold runtime.store.instantiate.Store.prepare_instance_loop8.body
    step with Interp.vec_index_given current.instances instIndex currentInst hfound as ⟨actual, hactual⟩
    subst actual
    simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Env.impl.elements, bind_ok, hsource]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.env.elements.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, .Err error, rfl, hstaged, hobjects, haccounted, hmetadata,
          currentInst, hfound, hsource, hbindings, himports, hsegments, hdatas, hmapData, hglobals, hglobalMap, hcontext, by simp⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        let segment := inst.module.module.env.elements.val[index.val]
        have hsegment : currentInst.module.module.env.elements.val[index.val]? = some segment := by
          rw [hsource]
          exact List.getElem?_eq_getElem hmore
        have hvalid : Itasca.Module.Segments.elementValid currentInst.module.module.env segment := by
          rw [hsource]
          exact valid segment (List.mem_of_getElem? (List.getElem?_eq_getElem hmore))
        have certificates := element_initializer_certificates current currentInst index segment
          (by simpa [hsource] using compiled) hsegment hvalid hbindings himports
        have room : current.elems.length < Usize.max := by omega
        have mapRoom : currentInst.elems.length < Usize.max := by omega
        step with add_instance_element_value_effect memory hooks floats allocator law current platform instIndex index
          currentInst segment hfound hsegment certificates hbindings room mapRoom
          sourceStore sourceInstance storeWf frameWf hcontext
          (by
            have sameType : Itasca.Module.Constants.referenceValueType segment.elem = elementValueType segment.elem := by
              cases segment.elem <;> rfl
            simpa only [sameType] using hvalid.2)
          as ⟨state, after, host', valueEffect, hhost'⟩
        have effect := valueEffect.content.typed.effect
        subst host'
        obtain ⟨nextInst, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextSize, nextStoreSize, nextData⟩ :=
          effect.context hfound hbindings himports hsegments
        have nextMetadata : InitializerFunctionMetadataAt store inst after instIndex :=
          ⟨nextInst, nextFound, (hmetadata.resolve hfound).trans (effect.function_metadata hfound nextFound)⟩
        have nextStaged := effect.staged hstaged fresh
        have nextObjects : objectCount after ≤ Usize.max := by simpa only [effect.object_count] using hobjects
        have counterCapacity := inst.module.module.env.elements.property
        step as ⟨next, hnext⟩
        refine ⟨nextStaged, nextObjects, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, nextBindings, nextImports, nextSegments, ?_,
          ?_, effect.data.trans hdatas, nextData.trans hmapData, effect.globals.trans hglobals, (effect.global_map hfound nextFound).trans hglobalMap, effect.source_context hfound nextFound hcontext, ?_⟩, ?_⟩
        · omega
        · omega
        · omega
        · intro success
          obtain ⟨produced, stored, previous⟩ := hmatching rfl
          obtain ⟨values, storedNext, nextValues⟩ := valueEffect.source_values stored previous success
          refine ⟨values, storedNext, ?_⟩
          rw [hnext, List.take_succ_eq_append_getElem hmore]
          exact nextValues
        · omega
    · rename_i stopped
      have atEnd : index.val = inst.module.module.env.elements.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, result, rfl, hstaged, hobjects, haccounted, hmetadata,
        currentInst, hfound, hsource, hbindings, himports, hsegments, hdatas, hmapData, hglobals, hglobalMap, hcontext, ?_⟩
      simpa only [atEnd, List.take_length] using hmatching
  · exact ⟨rfl, staged, objectBound, (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, bindings, imports, segments, mapCapacity, storeCapacity, rfl, rfl, rfl, rfl, sourceContext, matching⟩

end Itasca.Store

end

end
