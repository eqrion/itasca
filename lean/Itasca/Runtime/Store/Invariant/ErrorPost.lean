import Itasca.Runtime.Interp.Machine.Functions.CompiledFunctions
import Itasca.Runtime.Store.Invariant.FunctionTypingExtension
import Itasca.Runtime.Store.Invariant.CodeAgreement
import Itasca.Runtime.Store.Preparation.AllocationErrors
import Itasca.Runtime.Store.Api.DefineTable

/-!
Sections, each formerly its own module: CoreTypingExtension, DefinitionErrors, ErrorPost.
-/

/-! ## CoreTypingExtension -/

section

namespace Itasca.Runtime.Store
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
end Itasca.Runtime.Store

end

/-! ## DefinitionErrors -/

section

namespace Itasca.Runtime.Store
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
    (typed : ty.valtype = Interp.rawType value) (owned : Interp.ValueOwnedFits store.id value)
    (out : core.result.Result runtime.GlobalAddr runtime.ExecError × runtime.store.Store M)
    (run : runtime.store.Store.define_global_with memory allocator store ty value = .ok out) :
    ErrorAllowed ResourceError out.1 := by
  unfold runtime.store.Store.define_global_with at run
  simp only [check_value_owned memory store value owned, value_type_exact, typed,
    core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
    value_type_eq_self, bind_ok, lift, Bool.not_true] at run
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

end Itasca.Runtime.Store

end

/-! ## ErrorPost -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Attach a property of normal returns to a total extracted-call specification. -/
theorem normal_return_post {T : Type} {call : Result T} {post extra : T → Prop}
    (total : call ⦃ result => post result ⦄)
    (normal : ∀ result, call = .ok result → extra result) :
    call ⦃ result => post result ∧ extra result ⦄ := by
  obtain ⟨result, called, property⟩ := WP.spec_imp_exists total
  exact WP.exists_imp_spec ⟨result, called, property, normal result called⟩

end Itasca.Runtime.Store

end
