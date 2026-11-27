import Itasca.Runtime.Interp.Machine.CompiledFunctions
import Itasca.Runtime.Store.Invariant.HostSignature
import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Store.Preparation.AllocationStorage
import Itasca.Runtime.Store.Api.DefinitionsAndGrowth
import Itasca.Runtime.Store.Api.GlobalStagingAndCopy
import Itasca.Runtime.Store.Api.ObjectStaging
import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.Spec.TypingAndNumericOperations
import Itasca.Runtime.Store.Invariant.FunctionStaging

open WebAssembly

/-!
Proofs for Runtime / Store / Invariant.

This module collects ErrorPost, SemanticApi.
Each section documents its contracts and consumers.
-/

/-! ## ErrorPost -/

section

open Itasca.Representation

/-! ## CoreTypingExtension -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

theorem core_function_typed_code_agrees {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {before after : CodeInterpretation}
    (agrees : CodeAgreesOn store before after) {function : runtime.store.FuncInst}
    (typed : Interp.CoreFunctionTyped view before store function) :
    Interp.CoreFunctionTyped view after store function := by
  cases kind : function.code with
  | Host id =>
    simp only [Interp.CoreFunctionTyped, kind] at typed ⊢
    rwa [decode_function_code_agrees agrees]
  | Wasm ii fi =>
    simp only [Interp.CoreFunctionTyped, kind] at typed ⊢
    obtain ⟨inst, index, locals, body, found, source, bindings, typed⟩ := typed
    refine ⟨inst, index, locals, body, found, (agrees ii.val inst found fi.val).trans source, ?_, ?_⟩
    · rwa [decode_store_code_agrees view agrees]
    · rwa [decode_function_code_agrees agrees]

theorem core_functions_typed_code_agrees {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {before after : CodeInterpretation}
    (agrees : CodeAgreesOn store before after)
    (typed : Interp.CoreFunctionsTyped view before store) :
    Interp.CoreFunctionsTyped view after store :=
  fun function present => core_function_typed_code_agrees agrees (typed function present)

theorem core_function_typed_prefix {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (before after : runtime.store.Store M) (shape : Shape view before)
    (retained : StagedPrefix before after)
    (extension : Extend_store (decodeStore view code before) (decodeStore view code after))
    (function : runtime.store.FuncInst) (present : function ∈ before.funcs.val)
    (typed : Interp.CoreFunctionTyped view code before function) :
    Interp.CoreFunctionTyped view code after function := by
  have fnEq := decode_function_prefix code before after retained view shape function present
  cases kind : function.code with
  | Host id =>
    simp only [Interp.CoreFunctionTyped, kind] at typed ⊢
    rwa [fnEq]
  | Wasm ii fi =>
    simp only [Interp.CoreFunctionTyped, kind] at typed ⊢
    obtain ⟨inst, index, locals, body, found, source, bindings, typed⟩ := typed
    have bound := (List.getElem?_eq_some_iff.mp found).1
    have lookup := congrArg (fun xs => xs[ii.val]?) retained.instances
    have foundAfter : after.instances.val[ii.val]? = some inst := by
      simpa only [List.getElem?_take, if_pos bound, found] using lookup
    refine ⟨inst, index, locals, body, foundAfter, source, ?_, ?_⟩
    · rw [decode_instance_prefix before after retained inst (shape.instances inst (List.mem_of_getElem? found))]
      exact bindings.extend extension
    · rwa [fnEq]

theorem staged_core_function_typed_old_wf {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (before after : runtime.store.Store M) (shape : Shape view before)
    (sourceSyntax : StoreSyntax code before) (afterWf : wf_store (decodeStore view code after))
    (retained : StagedPrefix before after)
    (typed : Interp.CoreFunctionsTyped view code before)
    (function : runtime.store.FuncInst) (present : function ∈ before.funcs.val) :
    Interp.CoreFunctionTyped view code after function := by
  obtain ⟨functions, globals, tables, memories, elements, datas⟩ := decode_store_prefix view code before after shape retained
  have extension := store_prefix_extends _ _ (decode_store_wf view code before shape sourceSyntax) afterWf
    functions globals tables memories elements datas
  exact core_function_typed_prefix view code before after shape retained extension function present (typed function present)

theorem core_functions_typed_metadata {M : Type} {view : M → Slice U8}
    {code : CodeInterpretation} {before after : runtime.store.Store M}
    (functions : after.funcs = before.funcs) (types : after.types = before.types)
    (instances : after.instances = before.instances)
    (extension : Extend_store (decodeStore view code before) (decodeStore view code after))
    (typed : Interp.CoreFunctionsTyped view code before) : Interp.CoreFunctionsTyped view code after := by
  intro function present
  rw [functions] at present
  have body := typed function present
  have fnEq : decodeFunction code after function = decodeFunction code before function := by
    simp only [decodeFunction, decodeInstance, types, instances]
  cases kind : function.code with
  | Host id =>
    simp only [Interp.CoreFunctionTyped, kind] at body ⊢
    rwa [fnEq]
  | Wasm ii fi =>
    simp only [Interp.CoreFunctionTyped, kind] at body ⊢
    obtain ⟨inst, index, locals, instructions, found, source, bindings, body⟩ := body
    refine ⟨inst, index, locals, instructions, ?_, source, ?_, ?_⟩
    · rwa [instances]
    · simpa only [decodeInstance, types] using bindings.extend extension
    · rwa [fnEq]
end Itasca.Store

end

/-! ## DefinitionErrors -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

private theorem limits_success (limits : Itasca.wasm_types.Limits) (maximum : U32)
    (fit : LimitsFit limits maximum) : runtime.store.check_limits limits maximum = .ok (.Ok ()) := by
  obtain ⟨answer, called, result⟩ := WP.spec_imp_exists (check_limits_spec limits maximum)
  simpa [fit, result] using called

theorem define_table_errors {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (ty : Itasca.wasm_types.TableType)
    (fit : LimitsFit ty.limits core.num.U32.MAX)
    (out : core.result.Result runtime.TableAddr runtime.ExecError × runtime.store.Store M)
    (run : runtime.store.Store.define_table_with memory allocator store ty = .ok out) :
    ErrorAllowed ResourceError out.1 := by
  unfold runtime.store.Store.define_table_with at run
  simp only [limits_success ty.limits core.num.U32.MAX fit] at run
  repeat' allocation_error_step run using allocator, law

theorem define_global_errors {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (ty : Itasca.wasm_types.GlobalType) (value : runtime.Value)
    (typed : ty.valtype = Representation.rawType value) (owned : Representation.ValueOwnedFits store.id value)
    (out : core.result.Result runtime.GlobalAddr runtime.ExecError × runtime.store.Store M)
    (run : runtime.store.Store.define_global_with memory allocator store ty value = .ok out) :
    ErrorAllowed ResourceError out.1 := by
  unfold runtime.store.Store.define_global_with at run
  simp only [check_value_owned memory store value owned, value_type_exact, typed,
    core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
    value_type_eq_self, bind_ok, lift] at run
  repeat' allocation_error_step run using allocator, law

theorem define_memory_errors {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (ty : Itasca.wasm_types.MemType) (buffer : M)
    (fit : LimitsFit ty.limits 65536#u32)
    (length : (view buffer).length = ty.limits.min.val * 65536)
    (out : core.result.Result runtime.MemoryAddr runtime.ExecError × runtime.store.Store M)
    (run : runtime.store.Store.define_memory_with memory allocator store ty buffer = .ok out) :
    ErrorAllowed ResourceError out.1 := by
  have multiply : (UScalar.cast .U64 ty.limits.min) * 65536#u64
      ⦃ size => size.val = ty.limits.min.val * 65536 ⦄ := by
    step as ⟨size, sizeValue⟩
    scalar_tac
  obtain ⟨size, called, sizeValue⟩ := WP.spec_imp_exists multiply
  have sameSize : UScalar.cast .U64 (view buffer).len = size := by scalar_tac
  unfold runtime.store.Store.define_memory_with at run
  simp only [limits_success ty.limits 65536#u32 fit, lift, called,
    laws.read buffer, bind_ok, sameSize, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at run
  repeat' allocation_error_step run using allocator, law

end Itasca.Store

end

/-! ## ErrorPost -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- Attach a property of normal returns to a total extracted-call specification. -/
theorem normal_return_post {T : Type} {call : Result T} {post extra : T → Prop}
    (total : call ⦃ result => post result ⦄)
    (normal : ∀ result, call = .ok result → extra result) :
    call ⦃ result => post result ∧ extra result ⦄ := by
  obtain ⟨result, called, property⟩ := WP.spec_imp_exists total
  exact WP.exists_imp_spec ⟨result, called, property, normal result called⟩

end Itasca.Store

end

end

/-! ## SemanticApi -/

section

open Itasca.Representation

/-! ## BindingTyping -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std Itasca

theorem decode_global_type_source (global : runtime.store.GlobalInst) :
    (decodeGlobal global).TYPE = Translation.globalType global.ty := by
  cases global.ty.valtype <;> cases global.ty.mutability <;> rfl

theorem decode_elem_type_source (ty : wasm_types.ElemType) : Itasca.Translation.referenceType ty = Translation.referenceType ty := by
  cases ty <;> rfl

/-- Runtime import matching is exactly the generated limits subtyping rule. -/
theorem limits_match_sub (size : Nat) (maximum : Option U32) (required : wasm_types.Limits)
    (bound : size ≤ U32.max) (matching : LimitsMatch size maximum required) :
    Limits_sub (decodeLimits size maximum) (Translation.Environment.limitsType required) := by
  have actualWf := decode_limits_wf size maximum bound
  have sourceWf := decode_limits_wf required.min.val required.max (by scalar_tac)
  change wf_limits (Translation.Environment.limitsType required) at sourceWf
  cases actual : maximum with
  | none =>
    cases wanted : required.max with
    | none =>
      simpa only [decodeLimits, Translation.Environment.limitsType, actual, wanted, Option.map_none] using
        Limits_sub.eps size required.min.val matching.1
          (by simpa only [actual, decodeLimits, Option.map_none] using actualWf)
          (by simpa only [Translation.Environment.limitsType, wanted, Option.map_none] using sourceWf)
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
    have source : Translation.Environment.limitsType required =
        .mk_limits (.mk_uN required.min.val) (OMap (fun n => .mk_uN n) (required.max.map UScalar.val)) := by
      cases h : required.max <;> simp only [Translation.Environment.limitsType, h, Option.map_none, Option.map_some, OMap]
    rw [source]
    exact .max size value.val required.min.val _ matching.1 ordered
      (by simpa only [actual, decodeLimits, Option.map_some] using actualWf)
      (by simpa only [source] using sourceWf)

theorem imported_global_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (wellformed : wf_store (decodeStore view code store))
    (ty : wasm_types.GlobalType) (address : runtime.GlobalAddr) (linked : ImportedGlobal store ty address) :
    Externaddr_ok (decodeStore view code store) (.GLOBAL address.index.val) (.GLOBAL (Translation.globalType ty)) := by
  obtain ⟨_, global, found, typed⟩ := linked
  have read : (decodeStore view code store).GLOBALS[address.index.val]? = some (decodeGlobal global) := by
    simp only [decodeStore, List.getElem?_map, found, Option.map_some]
  have result := Externaddr_ok.global (decodeStore view code store) address.index.val (decodeGlobal global)
    (List.getElem?_eq_some_iff.mp read).1
    (by simp only [List.getElem!_eq_getElem?_getD, read, Option.getD_some]) wellformed
    (.externtype_case_1 _)
  simpa only [decode_global_type_source, typed] using result

theorem imported_table_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (wellformed : wf_store (decodeStore view code store))
    (shape : Shape view store) (ty : wasm_types.TableType) (address : runtime.TableAddr)
    (linked : ImportedTable store ty address) :
    Externaddr_ok (decodeStore view code store) (.TABLE address.index.val) (.TABLE (Translation.Environment.tableType ty)) := by
  obtain ⟨_, table, found, elementType, matching⟩ := linked
  have shaped := shape.tables table (List.mem_of_getElem? found)
  have read : (decodeStore view code store).TABLES[address.index.val]? = some (decodeTable table) := by
    simp only [decodeStore, List.getElem?_map, found, Option.map_some]
  have actualWf : wf_tabletype (decodeTable table).TYPE :=
    .tabletype_case_0 _ _ (decode_limits_wf _ _ shaped.1)
  have sourceWf : wf_tabletype (Translation.Environment.tableType ty) :=
    .tabletype_case_0 _ _ (decode_limits_wf ty.limits.min.val ty.limits.max (by scalar_tac))
  have base := Externaddr_ok.table (decodeStore view code store) address.index.val (decodeTable table)
    (List.getElem?_eq_some_iff.mp read).1
    (by simp only [List.getElem!_eq_getElem?_getD, read, Option.getD_some]) wellformed
    (.externtype_case_2 _ actualWf)
  apply Externaddr_ok.sub _ _ _ _ base ?_ wellformed (.externtype_case_2 _ sourceWf) (.externtype_case_2 _ actualWf)
  apply Externtype_sub.table
  · have subtype := limits_match_sub table.elements.length table.maximum ty.limits shaped.1 matching
    have eq : (decodeTable table).TYPE = .mk_tabletype (decodeLimits table.elements.length table.maximum)
        (Translation.referenceType ty.elem) := by
      simp only [decodeTable, elementType, decode_elem_type_source]
    rw [eq]
    exact .mk_Tabletype_sub _ _ _ subtype (by simpa only [eq] using actualWf) sourceWf
  · exact .externtype_case_2 _ actualWf
  · exact .externtype_case_2 _ sourceWf

theorem imported_memory_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (wellformed : wf_store (decodeStore view code store))
    (shape : Shape view store) (ty : wasm_types.MemType) (address : runtime.MemoryAddr)
    (linked : ImportedMemory view store ty address) :
    Externaddr_ok (decodeStore view code store) (.MEM address.index.val) (.MEM (Translation.Environment.memType ty)) := by
  obtain ⟨_, memory, found, matching⟩ := linked
  have shaped := shape.memories memory (List.mem_of_getElem? found)
  have bound : (view memory.buf).length / 65536 ≤ U32.max := by
    have upper := shaped.2.1
    scalar_tac
  have read : (decodeStore view code store).MEMS[address.index.val]? = some (decodeMemory view memory) := by
    simp only [decodeStore, List.getElem?_map, found, Option.map_some]
  have actualWf : wf_memtype (decodeMemory view memory).TYPE :=
    .memtype_case_0 _ (decode_limits_wf _ _ bound)
  have sourceWf : wf_memtype (Translation.Environment.memType ty) :=
    .memtype_case_0 _ (decode_limits_wf ty.limits.min.val ty.limits.max (by scalar_tac))
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

end Itasca.Store

end

/-! ## ObjectExtension -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- Replacing memory contents while retaining its maximum and not shrinking
its byte buffer satisfies generated memory-instance extension. -/
theorem decode_memory_extends {M : Type} (view : M → Slice U8)
    (before after : runtime.store.MemInst M)
    (maximum : after.maximum = before.maximum)
    (length : (view before.buf).length ≤ (view after.buf).length)
    (old : wf_meminst (decodeMemory view before))
    (fresh : wf_meminst (decodeMemory view after)) :
    Extend_meminst (decodeMemory view before) (decodeMemory view after) := by
  unfold decodeMemory at old fresh ⊢
  rw [maximum] at fresh ⊢
  simp only [decode_limits_option] at old fresh ⊢
  exact .mk_Extend_meminst _ _ _ _ _ (Nat.div_le_div_right length)
    (by simpa only [decodeBytes, List.length_map] using length) old fresh

/-- Table contents may change and grow while preserving reference type and
maximum; the generated extension relation retains both endpoint wf premises. -/
theorem decode_table_extends (before after : runtime.store.TableInst)
    (ty : after.ty = before.ty) (maximum : after.maximum = before.maximum)
    (length : before.elements.length ≤ after.elements.length)
    (old : wf_tableinst (decodeTable before)) (fresh : wf_tableinst (decodeTable after)) :
    Extend_tableinst (decodeTable before) (decodeTable after) := by
  unfold decodeTable at old fresh ⊢
  rw [ty, maximum] at fresh ⊢
  simp only [decode_limits_option] at old fresh ⊢
  exact .mk_Extend_tableinst _ _ _ _ _ _ length
    (by simpa only [List.length_map] using length) old fresh
end Itasca.Store

end

/-! ## SemanticApi -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

theorem decode_store_global_update {M : Type} (view : M → Slice U8)
    (code : CodeInterpretation) (s : runtime.store.Store M)
    (globals : alloc.vec.Vec runtime.store.GlobalInst) :
    decodeStore view code {s with globals} =
      {decodeStore view code s with GLOBALS := globals.val.map decodeGlobal} := by rfl

theorem decode_store_table_update {M : Type} (view : M → Slice U8)
    (code : CodeInterpretation) (s : runtime.store.Store M)
    (tables : alloc.vec.Vec runtime.store.TableInst) :
    decodeStore view code {s with tables} =
      {decodeStore view code s with TABLES := tables.val.map decodeTable} := by rfl

end Itasca.Store

end

end
