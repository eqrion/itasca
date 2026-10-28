import Itasca.Runtime.Store.Invariant.Syntax
import Itasca.Runtime.Store.Invariant.ValueShape

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem function_ref_typed (s : _root_.store) (hwf : wf_store s)
    (address : Nat) (haddress : address < s.FUNCS.length) :
    Ref_ok s (.REF_FUNC_ADDR address) .FUNCREF := by
  apply Ref_ok.func s address (s.FUNCS[address]!).TYPE
  · exact .func s address _ haddress rfl hwf (.externtype_case_0 _)
  · exact hwf
  · constructor

theorem decodeRef_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (hwf : wf_store (decodeStore view code s))
    (ty : Itasca.types.ElemType) (word : U64) (h : ReferenceShape s ty word) :
    Ref_ok (decodeStore view code s) (decodeRef ty word) (decodeElemType ty) := by
  by_cases hz : word.val = 0
  · simp [decodeRef, hz]
    exact .null _ _ hwf
  · cases ty with
    | FuncRef =>
      simp [decodeRef, hz, decodeElemType]
      apply function_ref_typed _ hwf
      simpa [ReferenceShape, hz, decodeStore] using h
    | ExternRef =>
      simp [decodeRef, hz, decodeElemType]
      exact .extern _ _ hwf

theorem refVal_eq (r : ref) : refVal r = val_ref r := by cases r <;> rfl

theorem decodeWords_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (hwf : wf_store (decodeStore view code s))
    (global : runtime.store.GlobalInst) (h : GlobalShape s global) :
    Val_ok (decodeStore view code s) (decodeWords global.ty.valtype global.lo global.hi)
      (Interp.sourceType global.ty.valtype) := by
  have hv := decodeWords_wf global.ty.valtype global.lo global.hi
  cases ht : global.ty.valtype with
  | I32 => exact .numtype _ .I32 _ hwf (by simpa [ht, decodeWords] using hv)
  | I64 => exact .numtype _ .I64 _ hwf (by simpa [ht, decodeWords] using hv)
  | F32 => exact .numtype _ .F32 _ hwf (by simpa [ht, decodeWords] using hv)
  | F64 => exact .numtype _ .F64 _ hwf (by simpa [ht, decodeWords] using hv)
  | V128 => exact .vectype _ .V128 _ hwf (by simpa [ht, decodeWords] using hv)
  | FuncRef =>
    have hr : ReferenceShape s .FuncRef global.lo := by
      simp only [GlobalShape, ht] at h
      exact h.1
    simpa [decodeWords, refVal_eq, Interp.sourceType, decodeElemType, valtype_reftype] using
      (Val_ok.reftype _ _ _ (decodeRef_typed view code s hwf .FuncRef global.lo hr) hwf)
  | ExternRef =>
    have hr : ReferenceShape s .ExternRef global.lo := by
      simp only [GlobalShape, ht] at h
      exact h.1
    simpa [decodeWords, refVal_eq, Interp.sourceType, decodeElemType, valtype_reftype] using
      (Val_ok.reftype _ _ _ (decodeRef_typed view code s hwf .ExternRef global.lo hr) hwf)

/-- Issued API values become typed specification values after ownership/index
checks. The source value retains float payloads and both v128 words exactly. -/
theorem value_in_store_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (hwf : wf_store (decodeStore view code s))
    (value : runtime.Value) (h : ValueInStore s value) :
    Val_ok (decodeStore view code s) (Interp.sourceValue value)
      (Interp.sourceType (Interp.rawType value)) := by
  cases value with
  | I32 bits => exact .numtype _ .I32 _ hwf (Interp.sourceValue_wf (.I32 bits))
  | I64 bits => exact .numtype _ .I64 _ hwf (Interp.sourceValue_wf (.I64 bits))
  | F32 bits => exact .numtype _ .F32 _ hwf (Interp.sourceValue_wf (.F32 bits))
  | F64 bits => exact .numtype _ .F64 _ hwf (Interp.sourceValue_wf (.F64 bits))
  | V128 bits => exact .vectype _ .V128 _ hwf (Interp.sourceValue_wf (.V128 bits))
  | FuncRef address =>
    cases address with
    | none => exact .reftype _ (.REF_NULL .FUNCREF) _ (.null _ _ hwf) hwf
    | some a =>
      apply Val_ok.reftype _ (.REF_FUNC_ADDR a.index.val) .FUNCREF _ hwf
      apply function_ref_typed _ hwf
      simpa [decodeStore] using h.2
  | ExternRef address =>
    cases address with
    | none => exact .reftype _ (.REF_NULL .EXTERNREF) _ (.null _ _ hwf) hwf
    | some a => exact .reftype _ (.REF_HOST_ADDR a.index.val) .EXTERNREF (.extern _ _ hwf) hwf

theorem decodeGlobal_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (hwf : wf_store (decodeStore view code s))
    (global : runtime.store.GlobalInst) (h : GlobalShape s global) :
    Globalinst_ok (decodeStore view code s) (decodeGlobal global) (decodeGlobal global).TYPE := by
  exact .mk_Globalinst_ok _ _ _ _ (.mk_Globaltype_ok _ _)
    (decodeWords_typed view code s hwf global h) hwf
    (.globalinst_case_ _ _ (decodeWords_wf _ _ _))

theorem decodeLimits_option (length : Nat) (maximum : Option U32) :
    decodeLimits length maximum = .mk_limits (.mk_uN length)
      (OMap (fun n => .mk_uN n) (maximum.map UScalar.val)) := by
  cases maximum <;> rfl

theorem decodeLimits_typed (length ceiling : Nat) (maximum : Option U32)
    (hceiling : ceiling ≤ U32.max) (hlength : length ≤ ceiling)
    (hmax : ∀ bound, maximum = some bound → length ≤ bound.val ∧ bound.val ≤ ceiling) :
    Limits_ok (decodeLimits length maximum) ceiling := by
  rw [decodeLimits_option]
  constructor
  · exact hlength
  · cases hm : maximum with
    | none => simp [OMap, Forall]
    | some bound =>
      intro value hvalue
      simp only [Option.map_some, Option.toList_some, List.mem_singleton] at hvalue
      subst value
      exact hmax bound hm
  · rw [← decodeLimits_option]
    exact decodeLimits_wf length maximum (Nat.le_trans hlength hceiling)

theorem decoded_tabletype_typed {M : Type} (s : runtime.store.Store M)
    (table : runtime.store.TableInst) (h : TableShape s table) :
    Tabletype_ok (decodeTable table).TYPE := by
  constructor
  · apply decodeLimits_typed table.elements.length _ table.maximum (by scalar_tac) (by have hb := h.1; scalar_tac)
    intro bound hb
    exact ⟨h.2.1 bound hb, by scalar_tac⟩
  · exact .tabletype_case_0 _ _ (decodeLimits_wf _ _ h.1)

theorem decoded_memtype_typed {M : Type} (view : M → Slice U8)
    (memory : runtime.store.MemInst M) (h : MemoryShape view memory) :
    Memtype_ok (decodeMemory view memory).TYPE := by
  constructor
  · apply decodeLimits_typed _ _ memory.maximum (by scalar_tac) (by simpa using h.2.1)
    exact h.2.2
  · exact .memtype_case_0 _ (decodeLimits_wf _ _ (by have hb := h.2.1; scalar_tac))

theorem decodeTable_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (hwf : wf_store (decodeStore view code s))
    (table : runtime.store.TableInst) (h : TableShape s table) :
    Tableinst_ok (decodeStore view code s) (decodeTable table) (decodeTable table).TYPE := by
  have ht := decoded_tabletype_typed s table h
  have hwt : wf_tabletype (decodeTable table).TYPE :=
    .tabletype_case_0 _ _ (decodeLimits_wf _ _ h.1)
  unfold decodeTable
  rw [decodeLimits_option]
  apply Tableinst_ok.mk_Tableinst_ok
  · simpa only [decodeTable, decodeLimits_option] using ht
  · intro value hvalue
    obtain ⟨word, hword, rfl⟩ := List.mem_map.mp hvalue
    exact decodeRef_typed view code s hwf table.ty word (h.2.2 word hword)
  · simp
  · exact hwf
  · constructor
    simpa only [decodeTable, decodeLimits_option] using hwt
  · simpa only [decodeTable, decodeLimits_option] using hwt

theorem decodeMemory_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (hwf : wf_store (decodeStore view code s))
    (memory : runtime.store.MemInst M) (h : MemoryShape view memory) :
    Meminst_ok (decodeStore view code s) (decodeMemory view memory) (decodeMemory view memory).TYPE := by
  have ht := decoded_memtype_typed view memory h
  have hwt : wf_memtype (decodeMemory view memory).TYPE :=
    .memtype_case_0 _ (decodeLimits_wf _ _ (by have hb := h.2.1; scalar_tac))
  unfold decodeMemory
  rw [decodeLimits_option]
  apply Meminst_ok.mk_Meminst_ok
  · simpa only [decodeMemory, decodeLimits_option] using ht
  · have hd := Nat.mod_add_div (view memory.buf).length 65536
    have ha := h.1
    simp [decodeBytes, Ki]
    change (view memory.buf).length = (view memory.buf).length / 65536 * 65536
    omega
  · exact hwf
  · constructor
    · simpa only [decodeMemory, decodeLimits_option] using hwt
    · exact decodeBytes_wf _
  · simpa only [decodeMemory, decodeLimits_option] using hwt

/-- Segment lengths come from validated binary counts. They remain explicit
structural bounds because dropped segments may be shorter than their sources. -/
structure SegmentBounds {M : Type} (s : runtime.store.Store M) : Prop where
  elements : ∀ element ∈ s.elems.val, element.refs.length < 2^32
  data : ∀ segment ∈ s.datas.val, segment.bytes.length < 2^32

theorem decodeElement_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (hwf : wf_store (decodeStore view code s))
    (element : runtime.store.ElemInst)
    (hrefs : ∀ word ∈ element.refs.val, ReferenceShape s element.ty word)
    (hbound : element.refs.length < 2^32) :
    Eleminst_ok (decodeStore view code s) (decodeElement element) (decodeElement element).TYPE := by
  constructor
  · intro value hvalue
    obtain ⟨word, hword, rfl⟩ := List.mem_map.mp hvalue
    exact decodeRef_typed view code s hwf element.ty word (hrefs word hword)
  · simpa using hbound
  · exact hwf

theorem decodeData_typed (s : _root_.store) (hwf : wf_store s)
    (data : runtime.store.DataInst) (hbound : data.bytes.length < 2^32) :
    Datainst_ok s (decodeData data) .OK := by
  constructor
  · simpa [decodeBytes] using hbound
  · exact hwf
  · exact .datainst_case_ _ (decodeBytes_wf _)

/-- Every non-function store component has the specification's semantic
instance typing. Function-body typing is separately supplied by compilation. -/
theorem decoded_components_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (shape : Shape view s) (hsyntax : StoreSyntax code s)
    (segments : SegmentBounds s) :
    let decoded := decodeStore view code s
    (∀ global ∈ decoded.GLOBALS, Globalinst_ok decoded global global.TYPE) ∧
    (∀ table ∈ decoded.TABLES, Tableinst_ok decoded table table.TYPE) ∧
    (∀ memory ∈ decoded.MEMS, Meminst_ok decoded memory memory.TYPE) ∧
    (∀ element ∈ decoded.ELEMS, Eleminst_ok decoded element element.TYPE) ∧
    (∀ data ∈ decoded.DATAS, Datainst_ok decoded data .OK) := by
  have hwf := decodeStore_wf view code s shape hsyntax
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro global hg
    obtain ⟨raw, hr, rfl⟩ := List.mem_map.mp hg
    exact decodeGlobal_typed view code s hwf raw (shape.globals raw hr)
  · intro table ht
    obtain ⟨raw, hr, rfl⟩ := List.mem_map.mp ht
    exact decodeTable_typed view code s hwf raw (shape.tables raw hr)
  · intro memory hm
    obtain ⟨raw, hr, rfl⟩ := List.mem_map.mp hm
    exact decodeMemory_typed view code s hwf raw (shape.memories raw hr)
  · intro element he
    obtain ⟨raw, hr, rfl⟩ := List.mem_map.mp he
    exact decodeElement_typed view code s hwf raw (shape.elements raw hr) (segments.elements raw hr)
  · intro data hd
    obtain ⟨raw, hr, rfl⟩ := List.mem_map.mp hd
    exact decodeData_typed _ hwf raw (segments.data raw hr)

end Itasca.Runtime.Store
