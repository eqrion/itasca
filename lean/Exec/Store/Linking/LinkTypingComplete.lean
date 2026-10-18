import Exec.Store.Invariant.BindingTyping
import Exec.Store.Api.ApiMetadata
import Exec.Spec.ExternalMatching
namespace Exec.Store
open Aeneas Aeneas.Std Itasca

/-- Limits subtyping supplies the exact comparison used by runtime linking. -/
theorem limits_compatible_match (size : Nat) (maximum : Option U32) (required : types.Limits)
    (source : Spec.LimitsCompatible (decodeLimits size maximum) (EnvTranslation.limitsType required)) :
    LimitsMatch size maximum required := by
  refine ⟨source.1, ?_⟩
  intro bound found
  obtain ⟨actual, actualFound, smaller⟩ := source.2 (.mk_uN bound.val)
    (by simp only [EnvTranslation.limitsType, found, Option.map_some])
  cases chosen : maximum with
  | none => simp only [decodeLimits, chosen, Option.map_none] at actualFound; cases actualFound
  | some value =>
    simp only [decodeLimits, chosen, Option.map_some, Option.some.injEq] at actualFound
    subst actual
    exact ⟨value, rfl, smaller⟩

theorem limits_sub_match (size : Nat) (maximum : Option U32) (required : types.Limits)
    (sub : Limits_sub (decodeLimits size maximum) (EnvTranslation.limitsType required)) :
    LimitsMatch size maximum required :=
  limits_compatible_match size maximum required (Spec.limits_sub_compatible sub)

private theorem func_translation (ty : types.FuncType) : decodeFuncType ty = EnvTranslation.funcType ty := by
  have same : Interp.sourceType = Translate.valueType := by funext t; cases t <;> rfl
  simp only [decodeFuncType, EnvTranslation.funcType, same]

/-- A source-typed function import selects the exact raw signature compared by linking. -/
theorem source_function_import_signature {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (address : runtime.FuncAddr) (function : runtime.store.Function)
    (signature required : types.FuncType)
    (found : store.funcs.val[address.index.val]? = some function)
    (signatureFound : store.types.val[function.signature.val]? = some signature)
    (typed : Externaddr_ok (decodeStore view code store) (.FUNC address.index.val)
      (.FUNC (EnvTranslation.funcType required))) : signature = required := by
  have compatible := Spec.externaddr_compatible typed
  have signatureBound := (List.getElem?_eq_some_iff.mp signatureFound).1
  have signatureEqual := (List.getElem?_eq_some_iff.mp signatureFound).2
  apply decodeFuncType_injective
  rw [func_translation required]
  simpa only [Spec.externalActualType, decodeStore, List.getElem!_eq_getElem?_getD,
    List.getElem?_map, found, Option.map_some, Option.getD_some, Spec.ExternalCompatible,
    decodeFunction_type code store function signatureBound, signatureEqual] using compatible

private theorem global_translation_injective : Function.Injective Translate.globalType := by
  intro a b equal
  have pair := globaltype.mk_globaltype.inj equal
  have mutable := Translate.mutability_injective pair.1
  have value := Translate.valueType_injective pair.2
  cases a; cases b
  cases mutable; cases value
  rfl

/-- Global external typing fixes both value type and mutability. -/
theorem source_global_import_type {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (address : runtime.GlobalAddr) (global : runtime.store.GlobalInstance)
    (required : types.GlobalType) (found : store.globals.val[address.index.val]? = some global)
    (typed : Externaddr_ok (decodeStore view code store) (.GLOBAL address.index.val)
      (.GLOBAL (Translate.globalType required))) : global.ty = required := by
  have compatible := Spec.externaddr_compatible typed
  apply global_translation_injective
  simpa only [Spec.externalActualType, decodeStore, List.getElem!_eq_getElem?_getD,
    List.getElem?_map, found, Option.map_some, Option.getD_some, Spec.ExternalCompatible,
    decodeGlobal_type_source] using compatible

/-- Memory external typing supplies the current-size/maximum comparison. -/
theorem source_memory_import_limits {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (address : runtime.MemoryAddr) (memory : runtime.store.Memory M)
    (required : types.MemType) (found : store.memories.val[address.index.val]? = some memory)
    (typed : Externaddr_ok (decodeStore view code store) (.MEM address.index.val)
      (.MEM (EnvTranslation.memType required))) :
    LimitsMatch ((view memory.buf).length / 65536) memory.maximum required.limits := by
  have compatible := Spec.externaddr_compatible typed
  apply limits_compatible_match
  simpa only [Spec.externalActualType, decodeStore, List.getElem!_eq_getElem?_getD,
    List.getElem?_map, found, Option.map_some, Option.getD_some, Spec.ExternalCompatible,
    decodeMemory, EnvTranslation.memType] using compatible

/-- Table external typing fixes its reference kind and compatible limits. -/
theorem source_table_import_type {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (address : runtime.TableAddr) (table : runtime.store.Table)
    (required : types.TableType) (found : store.tables.val[address.index.val]? = some table)
    (typed : Externaddr_ok (decodeStore view code store) (.TABLE address.index.val)
      (.TABLE (EnvTranslation.tableType required))) :
    table.ty = required.elem ∧ LimitsMatch table.elements.length table.maximum required.limits := by
  have compatible := Spec.externaddr_compatible typed
  simp only [Spec.externalActualType, decodeStore, List.getElem!_eq_getElem?_getD,
    List.getElem?_map, found, Option.map_some, Option.getD_some, Spec.ExternalCompatible,
    decodeTable, EnvTranslation.tableType] at compatible
  refine ⟨?_, limits_compatible_match _ _ _ compatible.2⟩
  have same := compatible.1
  cases ht : table.ty <;> cases hr : required.elem <;> simp_all [decodeElemType, Translate.referenceType]
end Exec.Store
