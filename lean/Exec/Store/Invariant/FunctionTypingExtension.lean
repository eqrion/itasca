import Exec.Abs.ModuleBindingsExtension
import Exec.Store.Invariant.Extension
import Exec.Store.Initialization.SegmentReady
namespace Exec.Store
open Aeneas Aeneas.Std

/-- Initializer mutations preserve decoded functions, including their indirect
signature and instance dependencies. -/
theorem SegmentAddressSpace.decoded_functions {M : Type} {before after : runtime.store.Store M}
    (metadata : SegmentAddressSpace before after) (view : M → Slice U8) (code : CodeInterpretation) :
    (decodeStore view code after).FUNCS = (decodeStore view code before).FUNCS := by
  have same : decodeFunction code after = decodeFunction code before := by
    funext function
    simp only [decodeFunction, decodeInstance, metadata.signatures, metadata.instances]
  simp only [decodeStore, metadata.functions, same]

end Exec.Store
