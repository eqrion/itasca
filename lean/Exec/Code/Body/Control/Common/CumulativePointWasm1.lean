import Exec.Code.Body.Reader.Common.CumulativeReaderCompilerPoint
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem CumulativeReaderCompilerPointWasm1.append_step {A : Type}
    {C initial before after types functions returns locals data env ctx bodyBt st out}
    (point : @CumulativeReaderCompilerPointWasm1 A C initial before types functions returns locals data env ctx bodyBt st)
    (extra : List (U32 × U32)) (pairs : after.function.indirect.val = before.function.indirect.val ++ extra)
    (step : ∀ future,
      StructuredReaderCompilerPointWasm1 (CumulativeEmission (after.function.indirect.val ++ future) C)
        initial before types functions returns locals data env ctx bodyBt st →
      StructuredReaderCompilerPointWasm1 (CumulativeEmission (after.function.indirect.val ++ future) C)
        initial after types functions returns locals data env ctx bodyBt out) :
    CumulativeReaderCompilerPointWasm1 C initial after types functions returns locals data env ctx bodyBt out := by
  intro future
  apply step future
  simpa only [pairs,List.append_assoc] using point (extra ++ future)

theorem CumulativeReaderCompilerPointWasm1.preserved_step {A : Type}
    {C initial before after types functions returns locals data env ctx bodyBt st out}
    (point : @CumulativeReaderCompilerPointWasm1 A C initial before types functions returns locals data env ctx bodyBt st)
    (pairs : after.function.indirect = before.function.indirect)
    (step : ∀ future,
      StructuredReaderCompilerPointWasm1 (CumulativeEmission (before.function.indirect.val ++ future) C)
        initial before types functions returns locals data env ctx bodyBt st →
      StructuredReaderCompilerPointWasm1 (CumulativeEmission (before.function.indirect.val ++ future) C)
        initial after types functions returns locals data env ctx bodyBt out) :
    CumulativeReaderCompilerPointWasm1 C initial after types functions returns locals data env ctx bodyBt out := by
  intro future
  simpa only [pairs] using step future (point future)

end Exec.Code
