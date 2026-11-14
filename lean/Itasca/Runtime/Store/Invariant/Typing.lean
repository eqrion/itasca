import Itasca.Runtime.Representation.StoreCapacity

/-!
Sections, each formerly its own module: Syntax, ValueShape, Typing.
-/

/-! ## Syntax -/

section

/-! Syntactic well-formedness of the decoded store. The named source certificates
below are supplied by compilation: export-name syntax and source function syntax.
They contain no execution-correctness premise. `wf_store` is SpecTec syntax;
it is deliberately distinct from the semantic typing judgment `Store_ok`. -/
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Source syntax attached to one compiled instance and its ghost source bodies. -/
structure InstanceSyntax (code : CodeInterpretation) (index : Nat)
    (inst : runtime.store.ModuleInst) : Prop where
  exportNames : ∀ entry ∈ inst.module.module.env.exports.val,
    wf_name (decodeName entry.name.val)
  functionCodes : ∀ function, function < inst.module.module.env.func_type_indices.length →
    wf_funccode (code index inst.module function)

/-- Each retained instance carries its independently checked source syntax. -/
def StoreSyntax {M : Type} (code : CodeInterpretation) (s : runtime.store.Store M) : Prop :=
  ∀ index inst, s.instances.val[index]? = some inst → InstanceSyntax code index inst

theorem decode_words_wf (ty : Itasca.wasm_types.ValueType) (lo hi : U64) :
    wf_val (decodeWords ty lo hi) := by
  cases ty with
  | I32 =>
    apply wf_val.val_case_0
    apply wf_num_.num__case_0 .I32 .I32 _ (by decide) ?_ rfl
    apply wf_uN.uN_case_0
    change 0 ≤ lo.val % 2^32 ∧ lo.val % 2^32 ≤ 4294967295
    have h := Nat.mod_lt lo.val (by decide : 0 < 2^32)
    omega
  | I64 =>
    apply wf_val.val_case_0
    apply wf_num_.num__case_0 .I64 .I64 _ (by decide) ?_ rfl
    apply wf_uN.uN_case_0
    change 0 ≤ lo.val ∧ lo.val ≤ 18446744073709551615
    scalar_tac
  | F32 =>
    apply wf_val.val_case_0
    exact .num__case_1 _ _ _ (SpecExt.Builtins.Float.floatOfBits_wf_32 _ (Nat.mod_lt _ (by decide))) rfl
  | F64 =>
    apply wf_val.val_case_0
    exact .num__case_1 _ _ _ (SpecExt.Builtins.Float.floatOfBits_wf_64 lo.val (by scalar_tac)) rfl
  | V128 =>
    apply wf_val.val_case_1 _ _ (by decide)
    apply wf_uN.uN_case_0
    change 0 ≤ lo.val + hi.val * 2^64 ∧ lo.val + hi.val * 2^64 ≤ 340282366920938463463374607431768211455
    scalar_tac
  | FuncRef =>
    simp only [decodeWords, decodeRef]
    split <;> constructor
  | ExternRef =>
    simp only [decodeWords, decodeRef]
    split <;> constructor

theorem decode_limits_wf (length : Nat) (maximum : Option U32) (h : length ≤ U32.max) :
    wf_limits (decodeLimits length maximum) := by
  apply wf_limits.limits_case_0
  · apply wf_uN.uN_case_0
    change 0 ≤ length ∧ length ≤ 4294967295
    scalar_tac
  · cases maximum with
    | none => simp [Forall]
    | some bound =>
      intro value hvalue
      simp only [Option.map_some, Option.toList_some, List.mem_singleton] at hvalue
      subst value
      apply wf_uN.uN_case_0
      change 0 ≤ bound.val ∧ bound.val ≤ 4294967295
      scalar_tac

theorem decode_bytes_wf (bytes : List U8) : Forall wf_byte (decodeBytes bytes) := by
  intro value hvalue
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hvalue
  apply wf_byte.byte_case_0
  scalar_tac

theorem decode_instance_wf {M : Type} (code : CodeInterpretation) (index : Nat)
    (s : runtime.store.Store M) (inst : runtime.store.ModuleInst) (h : InstanceSyntax code index inst) :
    wf_moduleinst (decodeInstance s inst) := by
  constructor
  intro entry hentry
  obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hentry
  unfold decodeExport
  exact .exportinst_case_ _ _ (h.exportNames raw hraw)

theorem decode_function_wf {M : Type} (code : CodeInterpretation)
    (s : runtime.store.Store M) (hsyntax : StoreSyntax code s)
    (function : runtime.store.FuncInst) (hshape : FunctionShape s function) :
    wf_funcinst (decodeFunction code s function) := by
  unfold decodeFunction
  dsimp only
  cases hc : function.code with
  | Host identity =>
    constructor
    · constructor
      change Forall wf_exportinst []
      simp [Forall]
    · constructor
  | Wasm instanceIndex functionIndex =>
    have h := hshape.2
    simp only [hc] at h
    obtain ⟨inst, hinst, hfunction⟩ := h
    simp only [hinst]
    constructor
    · exact decode_instance_wf code instanceIndex.val s inst (hsyntax _ _ hinst)
    · exact (hsyntax _ _ hinst).functionCodes functionIndex.val hfunction

/-- Structural representation bounds and source syntax establish SpecTec's
syntactic store well-formedness. This theorem does not assert `Store_ok`. -/
theorem decode_store_wf {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (shape : Shape view s) (hsyntax : StoreSyntax code s) :
    wf_store (decodeStore view code s) := by
  constructor
  · intro function hfunction
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hfunction
    exact decode_function_wf code s hsyntax raw (shape.functions raw hraw)
  · intro global hglobal
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hglobal
    exact .globalinst_case_ _ _ (decode_words_wf raw.ty.valtype raw.lo raw.hi)
  · intro table htable
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp htable
    apply wf_tableinst.tableinst_case_
    apply wf_tabletype.tabletype_case_0
    exact decode_limits_wf _ _ (shape.tables raw hraw).1
  · intro memory hmemory
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hmemory
    apply wf_meminst.meminst_case_
    · apply wf_memtype.memtype_case_0
      apply decode_limits_wf
      have h := (shape.memories raw hraw).2.1
      scalar_tac
    · exact decode_bytes_wf _
  · intro data hdata
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hdata
    exact .datainst_case_ _ (decode_bytes_wf _)

end Itasca.Runtime.Store

end

/-! ## ValueShape -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- API reference values name an existing object of this store. The additional
encoding bounds rule out the reserved null sentinel wrapping around. -/
def ValueInStore {M : Type} (s : runtime.store.Store M) (value : runtime.Value) : Prop :=
  Interp.ValueOwnedFits s.id value ∧ match value with
  | .FuncRef (some a) => a.index.val < s.funcs.length
  | .ExternRef (some a) => a.index.val < s.externs.length
  | _ => True

/-- Encoding an owned typed API value establishes the canonical global-word
invariant, including reference ownership and scalar high-word zeros. -/
theorem encode_global_shape {M : Type} (s : runtime.store.Store M)
    (value : runtime.Value) (ty : Itasca.wasm_types.GlobalType)
    (ht : ty.valtype = Interp.rawType value) (hv : ValueInStore s value) :
    runtime.value.encode value ⦃ words => GlobalShape s {ty, lo := words.1, hi := words.2} ⦄ := by
  cases value <;> simp only [runtime.value.encode, GlobalShape, ht, Interp.rawType]
  all_goals simp [lift]
  case I32 v => scalar_tac
  case F32 v => scalar_tac
  case V128 v => step
  case FuncRef address =>
    cases address with
    | none => simp [ReferenceShape]
    | some a =>
      simp only [ValueInStore, Interp.ValueOwnedFits] at hv
      simp
      step as ⟨word, hword⟩
      right
      scalar_tac
  case ExternRef address =>
    cases address with
    | none => simp [ReferenceShape]
    | some a =>
      simp only [ValueInStore, Interp.ValueOwnedFits] at hv
      simp
      step as ⟨word, hword⟩
      right
      scalar_tac


def elementValueType : Itasca.wasm_types.ElemType → Itasca.wasm_types.ValueType
  | .FuncRef => .FuncRef
  | .ExternRef => .ExternRef

theorem encode_reference_shape {M : Type} (s : runtime.store.Store M)
    (value : runtime.Value) (ty : Itasca.wasm_types.ElemType)
    (ht : elementValueType ty = Interp.rawType value) (hv : ValueInStore s value) :
    runtime.value.encode value ⦃ words => ReferenceShape s ty words.1 ⦄ := by
  apply WP.spec_mono (encode_global_shape s value {valtype := elementValueType ty, mutability := .Const} ht hv)
  intro words hwords
  cases ty <;> exact hwords.1

end Itasca.Runtime.Store

end

/-! ## Typing -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem function_ref_typed (s : _root_.store) (hwf : wf_store s)
    (address : Nat) (haddress : address < s.FUNCS.length) :
    Ref_ok s (.REF_FUNC_ADDR address) .FUNCREF := by
  apply Ref_ok.func s address (s.FUNCS[address]!).TYPE
  · exact .func s address _ haddress rfl hwf (.externtype_case_0 _)
  · exact hwf
  · constructor

theorem decode_ref_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (hwf : wf_store (decodeStore view code s))
    (ty : Itasca.wasm_types.ElemType) (word : U64) (h : ReferenceShape s ty word) :
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

theorem ref_val_eq (r : ref) : refVal r = val_ref r := by cases r <;> rfl

theorem decode_words_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (hwf : wf_store (decodeStore view code s))
    (global : runtime.store.GlobalInst) (h : GlobalShape s global) :
    Val_ok (decodeStore view code s) (decodeWords global.ty.valtype global.lo global.hi)
      (Interp.sourceType global.ty.valtype) := by
  have hv := decode_words_wf global.ty.valtype global.lo global.hi
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
    simpa [decodeWords, ref_val_eq, Interp.sourceType, decodeElemType, valtype_reftype] using
      (Val_ok.reftype _ _ _ (decode_ref_typed view code s hwf .FuncRef global.lo hr) hwf)
  | ExternRef =>
    have hr : ReferenceShape s .ExternRef global.lo := by
      simp only [GlobalShape, ht] at h
      exact h.1
    simpa [decodeWords, ref_val_eq, Interp.sourceType, decodeElemType, valtype_reftype] using
      (Val_ok.reftype _ _ _ (decode_ref_typed view code s hwf .ExternRef global.lo hr) hwf)

/-- Issued API values become typed specification values after ownership/index
checks. The source value retains float payloads and both v128 words exactly. -/
theorem value_in_store_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (hwf : wf_store (decodeStore view code s))
    (value : runtime.Value) (h : ValueInStore s value) :
    Val_ok (decodeStore view code s) (Interp.sourceValue value)
      (Interp.sourceType (Interp.rawType value)) := by
  cases value with
  | I32 bits => exact .numtype _ .I32 _ hwf (Interp.source_value_wf (.I32 bits))
  | I64 bits => exact .numtype _ .I64 _ hwf (Interp.source_value_wf (.I64 bits))
  | F32 bits => exact .numtype _ .F32 _ hwf (Interp.source_value_wf (.F32 bits))
  | F64 bits => exact .numtype _ .F64 _ hwf (Interp.source_value_wf (.F64 bits))
  | V128 bits => exact .vectype _ .V128 _ hwf (Interp.source_value_wf (.V128 bits))
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

theorem decode_global_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (hwf : wf_store (decodeStore view code s))
    (global : runtime.store.GlobalInst) (h : GlobalShape s global) :
    Globalinst_ok (decodeStore view code s) (decodeGlobal global) (decodeGlobal global).TYPE := by
  exact .mk_Globalinst_ok _ _ _ _ (.mk_Globaltype_ok _ _)
    (decode_words_typed view code s hwf global h) hwf
    (.globalinst_case_ _ _ (decode_words_wf _ _ _))

theorem decode_limits_option (length : Nat) (maximum : Option U32) :
    decodeLimits length maximum = .mk_limits (.mk_uN length)
      (OMap (fun n => .mk_uN n) (maximum.map UScalar.val)) := by
  cases maximum <;> rfl

theorem decode_limits_typed (length ceiling : Nat) (maximum : Option U32)
    (hceiling : ceiling ≤ U32.max) (hlength : length ≤ ceiling)
    (hmax : ∀ bound, maximum = some bound → length ≤ bound.val ∧ bound.val ≤ ceiling) :
    Limits_ok (decodeLimits length maximum) ceiling := by
  rw [decode_limits_option]
  constructor
  · exact hlength
  · cases hm : maximum with
    | none => simp [OMap, Forall]
    | some bound =>
      intro value hvalue
      simp only [Option.map_some, Option.toList_some, List.mem_singleton] at hvalue
      subst value
      exact hmax bound hm
  · rw [← decode_limits_option]
    exact decode_limits_wf length maximum (Nat.le_trans hlength hceiling)

theorem decoded_tabletype_typed {M : Type} (s : runtime.store.Store M)
    (table : runtime.store.TableInst) (h : TableShape s table) :
    Tabletype_ok (decodeTable table).TYPE := by
  constructor
  · apply decode_limits_typed table.elements.length _ table.maximum (by scalar_tac) (by have hb := h.1; scalar_tac)
    intro bound hb
    exact ⟨h.2.1 bound hb, by scalar_tac⟩
  · exact .tabletype_case_0 _ _ (decode_limits_wf _ _ h.1)

theorem decoded_memtype_typed {M : Type} (view : M → Slice U8)
    (memory : runtime.store.MemInst M) (h : MemoryShape view memory) :
    Memtype_ok (decodeMemory view memory).TYPE := by
  constructor
  · apply decode_limits_typed _ _ memory.maximum (by scalar_tac) (by simpa using h.2.1)
    exact h.2.2
  · exact .memtype_case_0 _ (decode_limits_wf _ _ (by have hb := h.2.1; scalar_tac))

theorem decode_table_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (hwf : wf_store (decodeStore view code s))
    (table : runtime.store.TableInst) (h : TableShape s table) :
    Tableinst_ok (decodeStore view code s) (decodeTable table) (decodeTable table).TYPE := by
  have ht := decoded_tabletype_typed s table h
  have hwt : wf_tabletype (decodeTable table).TYPE :=
    .tabletype_case_0 _ _ (decode_limits_wf _ _ h.1)
  unfold decodeTable
  rw [decode_limits_option]
  apply Tableinst_ok.mk_Tableinst_ok
  · simpa only [decodeTable, decode_limits_option] using ht
  · intro value hvalue
    obtain ⟨word, hword, rfl⟩ := List.mem_map.mp hvalue
    exact decode_ref_typed view code s hwf table.ty word (h.2.2 word hword)
  · simp
  · exact hwf
  · constructor
    simpa only [decodeTable, decode_limits_option] using hwt
  · simpa only [decodeTable, decode_limits_option] using hwt

theorem decode_memory_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (hwf : wf_store (decodeStore view code s))
    (memory : runtime.store.MemInst M) (h : MemoryShape view memory) :
    Meminst_ok (decodeStore view code s) (decodeMemory view memory) (decodeMemory view memory).TYPE := by
  have ht := decoded_memtype_typed view memory h
  have hwt : wf_memtype (decodeMemory view memory).TYPE :=
    .memtype_case_0 _ (decode_limits_wf _ _ (by have hb := h.2.1; scalar_tac))
  unfold decodeMemory
  rw [decode_limits_option]
  apply Meminst_ok.mk_Meminst_ok
  · simpa only [decodeMemory, decode_limits_option] using ht
  · have hd := Nat.mod_add_div (view memory.buf).length 65536
    have ha := h.1
    simp [decodeBytes, Ki]
    change (view memory.buf).length = (view memory.buf).length / 65536 * 65536
    omega
  · exact hwf
  · constructor
    · simpa only [decodeMemory, decode_limits_option] using hwt
    · exact decode_bytes_wf _
  · simpa only [decodeMemory, decode_limits_option] using hwt

/-- Segment lengths come from validated binary counts. They remain explicit
structural bounds because dropped segments may be shorter than their sources. -/
structure SegmentBounds {M : Type} (s : runtime.store.Store M) : Prop where
  elements : ∀ element ∈ s.elems.val, element.refs.length < 2^32
  data : ∀ segment ∈ s.datas.val, segment.bytes.length < 2^32

theorem decode_element_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (hwf : wf_store (decodeStore view code s))
    (element : runtime.store.ElemInst)
    (hrefs : ∀ word ∈ element.refs.val, ReferenceShape s element.ty word)
    (hbound : element.refs.length < 2^32) :
    Eleminst_ok (decodeStore view code s) (decodeElement element) (decodeElement element).TYPE := by
  constructor
  · intro value hvalue
    obtain ⟨word, hword, rfl⟩ := List.mem_map.mp hvalue
    exact decode_ref_typed view code s hwf element.ty word (hrefs word hword)
  · simpa using hbound
  · exact hwf

theorem decode_data_typed (s : _root_.store) (hwf : wf_store s)
    (data : runtime.store.DataInst) (hbound : data.bytes.length < 2^32) :
    Datainst_ok s (decodeData data) .OK := by
  constructor
  · simpa [decodeBytes] using hbound
  · exact hwf
  · exact .datainst_case_ _ (decode_bytes_wf _)

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
  have hwf := decode_store_wf view code s shape hsyntax
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro global hg
    obtain ⟨raw, hr, rfl⟩ := List.mem_map.mp hg
    exact decode_global_typed view code s hwf raw (shape.globals raw hr)
  · intro table ht
    obtain ⟨raw, hr, rfl⟩ := List.mem_map.mp ht
    exact decode_table_typed view code s hwf raw (shape.tables raw hr)
  · intro memory hm
    obtain ⟨raw, hr, rfl⟩ := List.mem_map.mp hm
    exact decode_memory_typed view code s hwf raw (shape.memories raw hr)
  · intro element he
    obtain ⟨raw, hr, rfl⟩ := List.mem_map.mp he
    exact decode_element_typed view code s hwf raw (shape.elements raw hr) (segments.elements raw hr)
  · intro data hd
    obtain ⟨raw, hr, rfl⟩ := List.mem_map.mp hd
    exact decode_data_typed _ hwf raw (segments.data raw hr)

end Itasca.Runtime.Store

end
