import Exec.Store.Invariant.SemanticRead

namespace Exec.Store
open Aeneas Aeneas.Std

theorem decodeFunction_type {M : Type} (code : CodeInterpretation)
    (s : runtime.store.Store M) (function : runtime.store.FuncInst)
    (hsignature : function.signature.val < s.types.length) :
    (decodeFunction code s function).TYPE = decodeFuncType s.types.val[function.signature.val] := by
  unfold decodeFunction
  dsimp only
  cases function.code <;> simp [List.getElem?_eq_getElem hsignature]
  split <;> rfl

end Exec.Store
