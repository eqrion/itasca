import Exec.Theorems.Api.CertifiedApi
namespace Exec.Theorems
open Aeneas Aeneas.Std

/-- Invocation and start already expose exact frame metadata. Their freshly
proved execution certificate therefore retains the stronger API invariant,
including export bounds, without any new callback correctness assumption. -/
theorem CertifiedApiStore.frame_metadata {emission allowed M view code before after}
    (prior : @CertifiedApiStore emission allowed M view code before)
    (fresh : CertifiedSupportedStore emission allowed view code after)
    (metadata : Interp.FrameStoreMetadata before after) :
    CertifiedApiStore emission allowed view code after :=
  ⟨fresh,prior.exportBounds.instances_eq metadata.instances⟩
end Exec.Theorems
