import Exec.Theorems.Composition.Certified.CertifiedCore
import Exec.Theorems.Composition.Certified.CertifiedFloatCore
namespace Exec.Code

theorem CoreFunctionCode.float_core {C params declared results body compiled epilogue}
    (certificate : CoreFunctionCode C params declared results body compiled epilogue) :
    FloatCoreFunctionCode C params declared results body compiled epilogue := by
  refine ⟨certificate.1, ?_⟩
  have original := certificate.2
  exact ⟨original.signature, original.locals, original.parameterSlots, original.localSlots,
    original.capacity, original.fetchBound, original.checked,
    original.bodyCode.map_emission (fun _ _ _ _ emission => .core emission),
    original.returnCode, original.endPosition⟩
end Exec.Code
namespace Exec.Theorems
open Aeneas Aeneas.Std

/-- Every existing mutable-core certificate embeds into the isolated float
extension without changing its source interpretation or runtime store. -/
theorem CertifiedCoreStore.float_core {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedCoreStore view code store) : CertifiedFloatCoreStore view code store := by
  refine ⟨certified.shape, certified.storeSyntax, certified.typed, ?_, ?_, certified.segmentBounds⟩
  · intro function member
    have original := certified.core function member
    cases shape : function.CODE with
    | HOST id => trivial
    | FUNC index locals body =>
      simp only [shape] at original ⊢
      exact fun i member => .core (original i member)
  · intro function member instanceIndex functionIndex defined
    obtain ⟨inst, compiled, signature, declared, body, epilogue,
      found, functionFound, signatureFound, source, table, types, certificate⟩ :=
      certified.compiled function member instanceIndex functionIndex defined
    exact ⟨inst, compiled, signature, declared, body, epilogue,
      found, functionFound, signatureFound, source, table, types, certificate.float_core⟩
end Exec.Theorems
