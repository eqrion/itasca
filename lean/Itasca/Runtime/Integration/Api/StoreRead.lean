import Itasca.Runtime.Integration.Api.StoreCreate
import Itasca.Runtime.Store.Api.Exports
import Itasca.Runtime.Compiler.Module.CompileDriverFrame
import Itasca.Runtime.Compiler.Local.Initializer

/-! Public store reads agree with the retained objects and their decoded source
components. Issued handles justify the unchecked index after ownership checks. -/

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Store Interp

/-- External identities are the exact values retained at the issued address. -/
@[step] theorem _root_.Itasca.runtime.store.Store.extern_identity.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (store : runtime.store.Store M)
    (address : runtime.ExternAddr) (issued : IssuedValue store (.ExternRef (some address))) :
    runtime.store.Store.extern_identity memory store address ⦃ result =>
      match result with
      | .Err error => error = .WrongStore ∧ address.store ≠ store.id
      | .Ok identity => address.store = store.id ∧ store.externs.val[address.index.val]? = some identity ⦄ := by
  unfold runtime.store.Store.extern_identity
  step with runtime.store.Store.check.spec memory store address.store as ⟨checked, checkEq⟩
  rw [checkEq]
  by_cases sameStore : address.store = store.id
  · simp only [if_pos sameStore, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have position := issued sameStore
    let object := store.externs.val[address.index.val]
    have found : store.externs.val[address.index.val]? = some object := List.getElem?_eq_getElem position
    step with vec_index_given store.externs address.index object found as ⟨actual, actualEq⟩
    subst actual
    exact ⟨sameStore, found⟩
  · simp only [if_neg sameStore, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    exact ⟨trivial, sameStore⟩

/-- A memory read exposes the platform view of the decoded memory bytes. -/
@[step] theorem _root_.Itasca.runtime.store.Store.memory.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (store : runtime.store.Store M) (address : runtime.MemoryAddr)
    (issued : ExternalIssued store (.Memory address)) :
    runtime.store.Store.memory memory store address ⦃ result =>
      match result with
      | .Err error => error = .WrongStore ∧ address.store ≠ store.id
      | .Ok bytes => address.store = store.id ∧ ∃ object,
        store.memories.val[address.index.val]? = some object ∧ bytes = view object.buf ∧
        (decodeStore view code store).MEMS[address.index.val]? = some (decodeMemory view object) ∧
        (decodeMemory view object).BYTES = decodeBytes bytes.val ⦄ := by
  unfold runtime.store.Store.memory
  step with runtime.store.Store.check.spec memory store address.store as ⟨checked, checkEq⟩
  rw [checkEq]
  by_cases sameStore : address.store = store.id
  · simp only [if_pos sameStore, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have position := issued sameStore
    let object := store.memories.val[address.index.val]
    have found : store.memories.val[address.index.val]? = some object := List.getElem?_eq_getElem position
    step with vec_index_given store.memories address.index object found as ⟨actual, actualEq⟩
    subst actual
    rw [laws.read]
    simp only [bind_ok, WP.spec_ok]
    refine ⟨sameStore, object, found, rfl, ?_, rfl⟩
    simp only [decodeStore, List.getElem?_map, found, Option.map_some]
  · simp only [if_neg sameStore, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    exact ⟨trivial, sameStore⟩

/-- Table size is the length of the decoded reference vector. -/
@[step] theorem _root_.Itasca.runtime.store.Store.table_size.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.TableAddr) (issued : ExternalIssued store (.Table address)) :
    runtime.store.Store.table_size memory store address ⦃ result =>
      match result with
      | .Err error => error = .WrongStore ∧ address.store ≠ store.id
      | .Ok size => address.store = store.id ∧ ∃ object,
        store.tables.val[address.index.val]? = some object ∧ size.val = object.elements.length ∧
        (decodeStore view code store).TABLES[address.index.val]? = some (decodeTable object) ∧
        size.val = (decodeTable object).REFS.length ⦄ := by
  unfold runtime.store.Store.table_size
  step with runtime.store.Store.check.spec memory store address.store as ⟨checked, checkEq⟩
  rw [checkEq]
  by_cases sameStore : address.store = store.id
  · simp only [if_pos sameStore, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have position := issued sameStore
    let object := store.tables.val[address.index.val]
    have found : store.tables.val[address.index.val]? = some object := List.getElem?_eq_getElem position
    step with vec_index_given store.tables address.index object found as ⟨actual, actualEq⟩
    subst actual
    have shape := held.shape.tables object (List.mem_of_getElem? found)
    step as ⟨size, sizeEq⟩
    have bounded := shape.1
    have exactSize : size.val = object.elements.length := by scalar_tac
    refine ⟨sameStore, object, found, exactSize, ?_, ?_⟩
    · simp only [decodeStore, List.getElem?_map, found, Option.map_some]
    · simpa only [decodeTable, List.length_map] using exactSize
  · simp only [if_neg sameStore, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    exact ⟨trivial, sameStore⟩

/-- Global reads return the value in the decoded global component. -/
@[step] theorem _root_.Itasca.runtime.store.Store.global.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.GlobalAddr) (issued : ExternalIssued store (.Global address)) :
    runtime.store.Store.global memory store address ⦃ result =>
      match result with
      | .Err error => error = .WrongStore ∧ address.store ≠ store.id
      | .Ok value => address.store = store.id ∧ ∃ object,
        store.globals.val[address.index.val]? = some object ∧
        (decodeStore view code store).GLOBALS[address.index.val]? = some (decodeGlobal object) ∧
        ValueInStore store value ∧ rawType value = object.ty.valtype ∧ sourceValue value = (decodeGlobal object).VALUE ⦄ := by
  unfold runtime.store.Store.global
  step with runtime.store.Store.check.spec memory store address.store as ⟨checked, checkEq⟩
  rw [checkEq]
  by_cases sameStore : address.store = store.id
  · simp only [if_pos sameStore, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have position := issued sameStore
    let object := store.globals.val[address.index.val]
    have found : store.globals.val[address.index.val]? = some object := List.getElem?_eq_getElem position
    step with vec_index_given store.globals address.index object found as ⟨actual, actualEq⟩
    subst actual
    have shape := held.shape.globals object (List.mem_of_getElem? found)
    have referenceBound : object.ty.valtype = .FuncRef ∨ object.ty.valtype = .ExternRef → object.lo.val ≤ Usize.max := by
      intro reference
      rcases reference with function | external
      · have words : ReferenceShape store .FuncRef object.lo ∧ object.hi = 0#u64 := by
          simpa only [GlobalShape, function] using shape
        exact words.1.word_bound store .FuncRef object.lo
      · have words : ReferenceShape store .ExternRef object.lo ∧ object.hi = 0#u64 := by
          simpa only [GlobalShape, external] using shape
        exact words.1.word_bound store .ExternRef object.lo
    obtain ⟨value, decodeRun, typed, decoded⟩ := WP.spec_imp_exists
      (decode_value_boundary object.ty.valtype object.lo object.hi store.id referenceBound)
    have owned := decode_global_owned store object shape
    rw [decodeRun] at owned
    simp only [WP.spec_ok] at owned
    rw [decodeRun]
    simp only [bind_ok, WP.spec_ok]
    refine ⟨sameStore, object, found, ?_, owned, typed, decoded⟩
    simp only [decodeStore, List.getElem?_map, found, Option.map_some]
  · simp only [if_neg sameStore, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    exact ⟨trivial, sameStore⟩

/-- Table reads expose exactly the selected decoded reference, or report the
checked element bound separately from a foreign table handle. -/
@[step] theorem _root_.Itasca.runtime.store.Store.table_get.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.TableAddr) (index : U32) (issued : ExternalIssued store (.Table address)) :
    runtime.store.Store.table_get memory store address index ⦃ result =>
      match result with
      | .Err error => (error = .WrongStore ∧ address.store ≠ store.id) ∨
        (error = .Trap .TableOutOfBounds ∧ address.store = store.id ∧ ∃ object,
          store.tables.val[address.index.val]? = some object ∧ object.elements.length ≤ index.val)
      | .Ok value => address.store = store.id ∧ ∃ object word,
        store.tables.val[address.index.val]? = some object ∧ object.elements.val[index.val]? = some word ∧
        (decodeStore view code store).TABLES[address.index.val]? = some (decodeTable object) ∧
        (decodeTable object).REFS[index.val]? = some (decodeRef object.ty word) ∧
        ValueInStore store value ∧ sourceValue value = refVal (decodeRef object.ty word) ⦄ := by
  unfold runtime.store.Store.table_get
  step with runtime.store.Store.check.spec memory store address.store as ⟨checked, checkEq⟩
  rw [checkEq]
  by_cases sameStore : address.store = store.id
  · simp only [if_pos sameStore, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have position := issued sameStore
    let object := store.tables.val[address.index.val]
    have found : store.tables.val[address.index.val]? = some object := List.getElem?_eq_getElem position
    step with vec_index_given store.tables address.index object found as ⟨actual, actualEq⟩
    subst actual
    simp only [lift, bind_ok]
    have castIndex := U32.cast_Usize_val_eq index
    by_cases outside : object.elements.length ≤ index.val
    · have outsideCast : UScalar.cast .Usize index ≥ object.elements.len := by scalar_tac
      simp only [object] at outsideCast
      simp only [if_pos outsideCast, WP.spec_ok]
      exact Or.inr ⟨trivial, sameStore, object, found, outside⟩
    · have inside : index.val < object.elements.length := by omega
      have insideCast : ¬UScalar.cast .Usize index ≥ object.elements.len := by scalar_tac
      simp only [object] at insideCast
      simp only [if_neg insideCast, element_value_type_exact, bind_ok, lift]
      let word := object.elements.val[index.val]
      have wordFound : object.elements.val[index.val]? = some word := List.getElem?_eq_getElem inside
      have castFound : object.elements.val[(UScalar.cast .Usize index).val]? = some word := by
        simpa only [castIndex] using wordFound
      step with vec_index_given object.elements (UScalar.cast .Usize index) word castFound as ⟨actualWord, wordEq⟩
      subst actualWord
      have shape := held.shape.tables object (List.mem_of_getElem? found)
      have reference := shape.2.2 word (List.mem_of_getElem? wordFound)
      have bound := reference.word_bound store object.ty word
      let global : runtime.store.GlobalInst :=
        { ty := { valtype := elementValueType object.ty, mutability := .Const }, lo := word, hi := 0#u64 }
      have globalShape : GlobalShape store global := by
        cases ty : object.ty <;>
          simpa only [global, GlobalShape, elementValueType, ty, and_true] using reference
      obtain ⟨value, decodeRun, typed, decoded⟩ := WP.spec_imp_exists
        (decode_value_boundary (elementValueType object.ty) word 0#u64 store.id (fun _ => bound))
      have owned := decode_global_owned store global globalShape
      change runtime.value.decode (elementValueType object.ty) word 0#u64 store.id ⦃ value => ValueInStore store value ⦄ at owned
      rw [decodeRun] at owned
      simp only [WP.spec_ok] at owned
      rw [decodeRun]
      simp only [bind_ok, WP.spec_ok]
      refine ⟨sameStore, object, word, found, wordFound, ?_, ?_, owned, ?_⟩
      · simp only [decodeStore, List.getElem?_map, found, Option.map_some]
      · simp only [decodeTable, List.getElem?_map, wordFound, Option.map_some]
      · cases ty : object.ty <;>
          simpa only [ty, elementValueType, decodeWords] using decoded
  · simp only [if_neg sameStore, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    exact Or.inl ⟨trivial, sameStore⟩

/-- Function type lookup returns the decoded type of the issued function. -/
@[step] theorem _root_.Itasca.runtime.store.Store.func_type.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.FuncAddr) (issued : ExternalIssued store (.Func address)) :
    runtime.store.Store.func_type memory store address ⦃ result =>
      match result with
      | .Err error => error = .WrongStore ∧ address.store ≠ store.id
      | .Ok signature => address.store = store.id ∧ ∃ function,
        store.funcs.val[address.index.val]? = some function ∧
        store.types.val[function.signature.val]? = some signature ∧
        (decodeStore view code store).FUNCS[address.index.val]? = some (decodeFunction code store function) ∧
        (decodeFunction code store function).TYPE = decodeFuncType signature ⦄ := by
  by_cases sameStore : address.store = store.id
  · let entry := held.call_entry address issued sameStore
    apply WP.spec_mono (func_type_lookup memory store address entry.function entry.signature
      sameStore entry.functionLookup entry.signatureLookup)
    intro result resultEq
    subst result
    refine ⟨sameStore, entry.function, entry.functionLookup, entry.signatureLookup, ?_, ?_⟩
    · simp only [decodeStore, List.getElem?_map, entry.functionLookup, Option.map_some]
    · exact (held.shape.function_signature_eq_iff code entry.function
        (List.mem_of_getElem? entry.functionLookup) entry.function.signature entry.signature entry.signatureLookup).mp rfl
  · rw [func_type_wrong_store memory store address sameStore]
    exact WP.spec.ret ⟨rfl, sameStore⟩

/-- Export lookup uses the first exact byte-name match. Returned handles are
issued and agree with the decoded instance exports, even for arbitrary queries. -/
@[step] theorem _root_.Itasca.runtime.store.Store.export.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.InstanceAddr) (query : Slice U8)
    (issued : address.store = store.id → address.index.val < store.instances.length) :
    runtime.store.Store.export memory store address query ⦃ result =>
      match result with
      | .Err error => error = .WrongStore ∧ address.store ≠ store.id
      | .Ok found => address.store = store.id ∧ ∃ inst,
        store.instances.val[address.index.val]? = some inst ∧
        found = exportSearch inst query 0 none ∧
        (found = none ↔ ∀ entry ∈ inst.module.module.env.exports.val, entry.name.val ≠ query.val) ∧
        ∀ external, found = some external → ExternalIssued store external ∧
          ∃ entry ∈ (decodeInstance store inst).EXPORTS,
            entry.NAME = decodeName query.val ∧ entry.ADDR = decodeExternal external ⦄ := by
  unfold runtime.store.Store.export
  step with runtime.store.Store.check.spec memory store address.store as ⟨checked, checkEq⟩
  rw [checkEq]
  by_cases sameStore : address.store = store.id
  · simp only [if_pos sameStore, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have position := issued sameStore
    let inst := store.instances.val[address.index.val]
    have lookup : store.instances.val[address.index.val]? = some inst := List.getElem?_eq_getElem position
    have shape := held.shape.instances inst (List.mem_of_getElem? lookup)
    have bounds := held.exportBounds address.index.val inst lookup
    step with vec_index_given store.instances address.index inst lookup as ⟨actual, actualEq⟩
    subst actual
    step with runtime.compiler.ExecutableModule.env.spec inst.module as ⟨env, envEq⟩
    subst env
    step with runtime.store.Store.export_loop.spec store inst bounds shape query 0#usize none
      (by scalar_tac) as ⟨found, foundEq⟩
    refine ⟨sameStore, inst, lookup, foundEq, ?_, ?_⟩
    · rw [foundEq]
      exact exportSearch_none_iff inst query
    · intro external returned
      obtain ⟨entry, member, named, resolved⟩ :=
        exportSearch_some inst query external (foundEq.symm.trans returned)
      refine ⟨?_, decodeExport inst entry, ?_, ?_, ?_⟩
      · rw [← resolved]
        exact resolveExport_issued store inst bounds shape entry member
      · exact List.mem_map.mpr ⟨entry, member, rfl⟩
      · change decodeName entry.name.val = decodeName query.val
        rw [named]
      · rw [← resolved]
        exact resolveExport_source store inst bounds shape entry member
  · simp only [if_neg sameStore, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    exact ⟨trivial, sameStore⟩

end Itasca.Runtime.Integration
