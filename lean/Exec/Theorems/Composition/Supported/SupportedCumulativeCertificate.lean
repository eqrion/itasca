import Exec.Theorems.Composition.Certified.CertifiedSupported
import Exec.Theorems.Composition.Certified.CertifiedCumulative
import Exec.Interp.Cumulative.Certificates
import Exec.Abs.Supported.Cumulative
namespace Exec.Theorems
open Aeneas Aeneas.Std

theorem CertifiedCumulativeStore.supported {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedCumulativeStore view code store) :
    CertifiedSupportedStore Interp.Cumulative.emission Abs.CumulativeInstr view code store :=
  ⟨certified.shape,certified.storeSyntax,certified.typed,certified.core,
    Interp.Cumulative.compiled_functions certified.compiled,certified.segmentBounds⟩

theorem CertifiedSupportedStore.cumulative {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedSupportedStore Interp.Cumulative.emission Abs.CumulativeInstr view code store) :
    CertifiedCumulativeStore view code store :=
  ⟨certified.shape,certified.storeSyntax,certified.typed,certified.supported,Interp.Cumulative.compiled_functions_legacy certified.compiled,certified.segmentBounds⟩
end Exec.Theorems
