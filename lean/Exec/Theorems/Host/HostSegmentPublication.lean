import Exec.Theorems.Api.ExecutableInv
import Exec.Interp.Relations.FrameStorePrefix
import Exec.Store.Initialization.SegmentPublication
namespace Exec.Interp
open Aeneas Aeneas.Std
end Exec.Interp

namespace Exec.Theorems
open Aeneas Aeneas.Std

/-- Explicit complete-invariant retention and raw frame-prefix retention give
an exact segment publication ledger, including host-created instances. No
segment-count equality or host semantic law is inferred from source extension. -/
theorem ExecutableInv.segment_publication {M : Type} {view : M → Slice U8}
    {oldCode newCode : Store.CodeInterpretation} {before after : runtime.store.Store M}
    (old : ExecutableInv view oldCode before) (fresh : ExecutableInv view newCode after)
    (retained : Interp.FrameStorePrefix before after) : Store.SegmentPublication before after :=
  .of_accounting retained.instances old.segmentAccounting fresh.segmentAccounting

end Exec.Theorems
