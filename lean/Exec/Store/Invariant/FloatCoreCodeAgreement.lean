import Exec.Store.Invariant.FloatCoreFunctionTables
import Exec.Store.Invariant.CodeAgreement
namespace Exec.Store
open Aeneas Aeneas.Std

theorem float_core_compiled_functions_code_agrees {M : Type} {store : runtime.store.Store M}
    {before after : CodeInterpretation} (agrees : CodeAgreesOn store before after)
    (compiled : Interp.FloatCoreCompiledFunctions before store) : Interp.FloatCoreCompiledFunctions after store := by
  intro function present instanceIndex functionIndex defined
  obtain ⟨inst, code, signature, declared, body, epilogue,
    found, functionFound, signatureFound, source, table, types, certificate⟩ :=
    compiled function present instanceIndex functionIndex defined
  exact ⟨inst, code, signature, declared, body, epilogue, found, functionFound,
    signatureFound, (agrees instanceIndex.val inst found functionIndex.val).trans source, table, types, certificate⟩
end Exec.Store
