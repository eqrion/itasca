import Itasca.Runtime.Interp.Machine.Functions.Typing
import Itasca.Runtime.Store.Invariant.FunctionTypingExtension
import Itasca.Runtime.Store.Invariant.CodeAgreement
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
    rwa [decodeFunction_code_agrees agrees]
  | Wasm ii fi =>
    simp only [Interp.CoreFunctionTyped, kind] at typed ⊢
    obtain ⟨inst, index, locals, body, found, source, bindings, typed⟩ := typed
    refine ⟨inst, index, locals, body, found, (agrees ii.val inst found fi.val).trans source, ?_, ?_⟩
    · rwa [decodeStore_code_agrees view agrees]
    · rwa [decodeFunction_code_agrees agrees]

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
  have fnEq := decodeFunction_prefix code before after retained view shape function present
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
    · rw [decodeInstance_prefix before after retained inst (shape.instances inst (List.mem_of_getElem? found))]
      exact bindings.extend extension
    · rwa [fnEq]

theorem staged_core_function_typed_old_wf {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (before after : runtime.store.Store M) (shape : Shape view before)
    (sourceSyntax : StoreSyntax code before) (afterWf : wf_store (decodeStore view code after))
    (retained : StagedPrefix before after)
    (typed : Interp.CoreFunctionsTyped view code before)
    (function : runtime.store.FuncInst) (present : function ∈ before.funcs.val) :
    Interp.CoreFunctionTyped view code after function := by
  obtain ⟨functions, globals, tables, memories, elements, datas⟩ := decodeStore_prefix view code before after shape retained
  have extension := store_prefix_extends _ _ (decodeStore_wf view code before shape sourceSyntax) afterWf
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
