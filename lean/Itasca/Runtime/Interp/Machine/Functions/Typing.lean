import Itasca.Runtime.Interp.Relations.CompiledFunctions
import Itasca.Runtime.Compiler.Local.Relations.Function.CoreFunctionContext
import Itasca.Runtime.SourceMachine.Typing

/-!
The completed module context has no ambient function-local declarations.

Main declarations: `moduleSourceContext` and `CoreFunctionTyped`. A direct consumer is `Interp.Machine.Calls.CallLookup`.
-/

namespace Itasca.Runtime.Code
/-- The completed module context has no ambient function-local declarations. -/
def moduleSourceContext (module : runtime.compiler.ExecutableModule) : context :=
  {moduleFunctionContext module [] [] with RETURN := none}
end Itasca.Runtime.Code
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Source typing uses the exact canonical context retained by the compiler,
not an existential alternative with unrelated global or memory declarations. -/
def CoreFunctionTyped {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (function : runtime.store.FuncInst) : Prop :=
  match function.code with
  | .Host _ => Functype_ok (Store.decodeFunction code store function).TYPE
  | .Wasm instanceIndex functionIndex =>
      ∃ inst index locals body,
        store.instances.val[instanceIndex.val]? = some inst ∧
        code instanceIndex.val inst.module functionIndex.val = .FUNC index locals body ∧
        Abs.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst)
          (Code.moduleSourceContext inst.module) ∧
        Func_ok (Code.moduleSourceContext inst.module) (.FUNC index locals body)
          (Store.decodeFunction code store function).TYPE

def CoreFunctionsTyped {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) : Prop :=
  ∀ function ∈ store.funcs.val, CoreFunctionTyped view code store function

theorem CoreFunctionsTyped.functions_typed {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (typed : CoreFunctionsTyped view code store) :
    Abs.FunctionsTyped (Store.decodeStore view code store) := by
  intro fn member
  obtain ⟨function, present, rfl⟩ := List.mem_map.mp member
  have body := typed function present
  cases kind : function.code with
  | Host id => simpa only [CoreFunctionTyped, kind, Store.decodeFunction] using body
  | Wasm ii fi =>
    simp only [CoreFunctionTyped, kind] at body
    obtain ⟨inst, index, locals, instructions, found, source, bindings, body⟩ := body
    simp only [Store.decodeFunction, kind, found, source] at body ⊢
    exact ⟨Code.moduleSourceContext inst.module, bindings, rfl, rfl, rfl, body⟩
end Itasca.Runtime.Interp
