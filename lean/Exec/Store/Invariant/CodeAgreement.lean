import Exec.Store.Invariant.FunctionTables
namespace Exec.Store
open Aeneas Aeneas.Std

/-- Assigning source code at fresh instance keys leaves every existing
function's decoded source unchanged, including absent-instance fallbacks. -/
theorem decodeFunction_code_agrees {M : Type} {store : runtime.store.Store M}
    {before after : CodeInterpretation} (agrees : CodeAgreesOn store before after)
    (function : runtime.store.Function) :
    decodeFunction after store function = decodeFunction before store function := by
  cases kind : function.code with
  | Host id => simp only [decodeFunction, kind]
  | Wasm index fn =>
    cases found : store.instances.val[index.val]? with
    | none => simp only [decodeFunction, kind, found]
    | some inst => simp only [decodeFunction, kind, found, agrees index.val inst found fn.val]

theorem decodeStore_code_agrees {M : Type} (view : M → Slice U8)
    {store : runtime.store.Store M} {before after : CodeInterpretation}
    (agrees : CodeAgreesOn store before after) :
    decodeStore view after store = decodeStore view before store := by
  have functions : store.funcs.val.map (decodeFunction after store) =
      store.funcs.val.map (decodeFunction before store) := by
    apply List.map_congr_left
    intro function _
    exact decodeFunction_code_agrees agrees function
  unfold decodeStore
  rw [functions]

/-- Retained compiled-function certificates depend only on source code at
actual installed instances. No execution property is assumed. -/
theorem compiled_functions_code_agrees {M : Type} {store : runtime.store.Store M}
    {before after : CodeInterpretation} (agrees : CodeAgreesOn store before after)
    (compiled : Interp.CompiledFunctions before store) : Interp.CompiledFunctions after store := by
  intro function present instanceIndex functionIndex defined
  obtain ⟨inst, code, signature, functions, declared, body, epilogue,
    found, functionFound, signatureFound, source, table, certificate⟩ :=
    compiled function present instanceIndex functionIndex defined
  exact ⟨inst, code, signature, functions, declared, body, epilogue, found, functionFound,
    signatureFound, (agrees instanceIndex.val inst found functionIndex.val).trans source, table, certificate⟩
end Exec.Store
