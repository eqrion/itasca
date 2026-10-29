import Itasca.Runtime.Store.Invariant.FunctionTables
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Assigning source code at fresh instance keys leaves every existing
function's decoded source unchanged, including absent-instance fallbacks. -/
theorem decode_function_code_agrees {M : Type} {store : runtime.store.Store M}
    {before after : CodeInterpretation} (agrees : CodeAgreesOn store before after)
    (function : runtime.store.FuncInst) :
    decodeFunction after store function = decodeFunction before store function := by
  cases kind : function.code with
  | Host id => simp only [decodeFunction, kind]
  | Wasm index fn =>
    cases found : store.instances.val[index.val]? with
    | none => simp only [decodeFunction, kind, found]
    | some inst => simp only [decodeFunction, kind, found, agrees index.val inst found fn.val]

theorem decode_store_code_agrees {M : Type} (view : M → Slice U8)
    {store : runtime.store.Store M} {before after : CodeInterpretation}
    (agrees : CodeAgreesOn store before after) :
    decodeStore view after store = decodeStore view before store := by
  have functions : store.funcs.val.map (decodeFunction after store) =
      store.funcs.val.map (decodeFunction before store) := by
    apply List.map_congr_left
    intro function _
    exact decode_function_code_agrees agrees function
  unfold decodeStore
  rw [functions]

end Itasca.Runtime.Store
