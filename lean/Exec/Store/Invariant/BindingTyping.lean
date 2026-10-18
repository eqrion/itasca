import Exec.Store.Api.GlobalTypeMap
import Exec.Store.Api.TableMemoryBindings
import Exec.Store.Invariant.Typing
import Exec.Store.Invariant.FunctionTables
namespace Exec.Store
open Aeneas Aeneas.Std Itasca

theorem decodeGlobal_type_source (global : runtime.store.GlobalInstance) :
    (decodeGlobal global).TYPE = Translate.globalType global.ty := by
  cases global.ty.valtype <;> cases global.ty.mutability <;> rfl

theorem decodeElemType_source (ty : types.ElemType) : decodeElemType ty = Translate.referenceType ty := by
  cases ty <;> rfl

/-- Runtime import matching is exactly the generated limits subtyping rule. -/
theorem limits_match_sub (size : Nat) (maximum : Option U32) (required : types.Limits)
    (bound : size ≤ U32.max) (matching : LimitsMatch size maximum required) :
    Limits_sub (decodeLimits size maximum) (EnvTranslation.limitsType required) := by
  have actualWf := decodeLimits_wf size maximum bound
  have sourceWf := decodeLimits_wf required.min.val required.max (by scalar_tac)
  change wf_limits (EnvTranslation.limitsType required) at sourceWf
  cases actual : maximum with
  | none =>
    cases wanted : required.max with
    | none =>
      simpa only [decodeLimits, EnvTranslation.limitsType, actual, wanted, Option.map_none] using
        Limits_sub.eps size required.min.val matching.1
          (by simpa only [actual, decodeLimits, Option.map_none] using actualWf)
          (by simpa only [EnvTranslation.limitsType, wanted, Option.map_none] using sourceWf)
    | some value =>
      obtain ⟨other, impossible, _⟩ := matching.2 value wanted
      rw [actual] at impossible
      contradiction
  | some value =>
    have ordered : Forall (fun n => value.val ≤ n) (required.max.map UScalar.val).toList := by
      intro n member
      cases wanted : required.max with
      | none => simp [wanted] at member
      | some requiredMax =>
        simp only [wanted, Option.map_some, Option.toList_some, List.mem_singleton] at member
        subst n
        obtain ⟨other, same, le⟩ := matching.2 requiredMax wanted
        have equal : other = value := Option.some.inj (same.symm.trans actual)
        simpa only [equal] using le
    have source : EnvTranslation.limitsType required =
        .mk_limits (.mk_uN required.min.val) (OMap (fun n => .mk_uN n) (required.max.map UScalar.val)) := by
      cases h : required.max <;> simp only [EnvTranslation.limitsType, h, Option.map_none, Option.map_some, OMap]
    rw [source]
    exact .max size value.val required.min.val _ matching.1 ordered
      (by simpa only [actual, decodeLimits, Option.map_some] using actualWf)
      (by simpa only [source] using sourceWf)

theorem imported_global_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (wellformed : wf_store (decodeStore view code store))
    (ty : types.GlobalType) (address : runtime.GlobalAddr) (linked : ImportedGlobal store ty address) :
    Externaddr_ok (decodeStore view code store) (.GLOBAL address.index.val) (.GLOBAL (Translate.globalType ty)) := by
  obtain ⟨_, global, found, typed⟩ := linked
  have read : (decodeStore view code store).GLOBALS[address.index.val]? = some (decodeGlobal global) := by
    simp only [decodeStore, List.getElem?_map, found, Option.map_some]
  have result := Externaddr_ok.global (decodeStore view code store) address.index.val (decodeGlobal global)
    (List.getElem?_eq_some_iff.mp read).1
    (by simp only [List.getElem!_eq_getElem?_getD, read, Option.getD_some]) wellformed
    (.externtype_case_1 _)
  simpa only [decodeGlobal_type_source, typed] using result

theorem imported_table_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (wellformed : wf_store (decodeStore view code store))
    (shape : Shape view store) (ty : types.TableType) (address : runtime.TableAddr)
    (linked : ImportedTable store ty address) :
    Externaddr_ok (decodeStore view code store) (.TABLE address.index.val) (.TABLE (EnvTranslation.tableType ty)) := by
  obtain ⟨_, table, found, elementType, matching⟩ := linked
  have shaped := shape.tables table (List.mem_of_getElem? found)
  have read : (decodeStore view code store).TABLES[address.index.val]? = some (decodeTable table) := by
    simp only [decodeStore, List.getElem?_map, found, Option.map_some]
  have actualWf : wf_tabletype (decodeTable table).TYPE :=
    .tabletype_case_0 _ _ (decodeLimits_wf _ _ shaped.1)
  have sourceWf : wf_tabletype (EnvTranslation.tableType ty) :=
    .tabletype_case_0 _ _ (decodeLimits_wf ty.limits.min.val ty.limits.max (by scalar_tac))
  have base := Externaddr_ok.table (decodeStore view code store) address.index.val (decodeTable table)
    (List.getElem?_eq_some_iff.mp read).1
    (by simp only [List.getElem!_eq_getElem?_getD, read, Option.getD_some]) wellformed
    (.externtype_case_2 _ actualWf)
  apply Externaddr_ok.sub _ _ _ _ base ?_ wellformed (.externtype_case_2 _ sourceWf) (.externtype_case_2 _ actualWf)
  apply Externtype_sub.table
  · have subtype := limits_match_sub table.elements.length table.maximum ty.limits shaped.1 matching
    have eq : (decodeTable table).TYPE = .mk_tabletype (decodeLimits table.elements.length table.maximum)
        (Translate.referenceType ty.elem) := by
      simp only [decodeTable, elementType, decodeElemType_source]
    rw [eq]
    exact .mk_Tabletype_sub _ _ _ subtype (by simpa only [eq] using actualWf) sourceWf
  · exact .externtype_case_2 _ actualWf
  · exact .externtype_case_2 _ sourceWf

theorem imported_memory_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (wellformed : wf_store (decodeStore view code store))
    (shape : Shape view store) (ty : types.MemType) (address : runtime.MemoryAddr)
    (linked : ImportedMemory view store ty address) :
    Externaddr_ok (decodeStore view code store) (.MEM address.index.val) (.MEM (EnvTranslation.memType ty)) := by
  obtain ⟨_, memory, found, matching⟩ := linked
  have shaped := shape.memories memory (List.mem_of_getElem? found)
  have bound : (view memory.buf).length / 65536 ≤ U32.max := by
    have upper := shaped.2.1
    scalar_tac
  have read : (decodeStore view code store).MEMS[address.index.val]? = some (decodeMemory view memory) := by
    simp only [decodeStore, List.getElem?_map, found, Option.map_some]
  have actualWf : wf_memtype (decodeMemory view memory).TYPE :=
    .memtype_case_0 _ (decodeLimits_wf _ _ bound)
  have sourceWf : wf_memtype (EnvTranslation.memType ty) :=
    .memtype_case_0 _ (decodeLimits_wf ty.limits.min.val ty.limits.max (by scalar_tac))
  have base := Externaddr_ok.mem (decodeStore view code store) address.index.val (decodeMemory view memory)
    (List.getElem?_eq_some_iff.mp read).1
    (by simp only [List.getElem!_eq_getElem?_getD, read, Option.getD_some]) wellformed
    (.externtype_case_3 _ actualWf)
  apply Externaddr_ok.sub _ _ _ _ base ?_ wellformed (.externtype_case_3 _ sourceWf) (.externtype_case_3 _ actualWf)
  apply Externtype_sub.mem
  · exact .mk_Memtype_sub _ _
      (limits_match_sub ((view memory.buf).length / 65536) memory.maximum ty.limits bound matching) actualWf sourceWf
  · exact .externtype_case_3 _ actualWf
  · exact .externtype_case_3 _ sourceWf

end Exec.Store
