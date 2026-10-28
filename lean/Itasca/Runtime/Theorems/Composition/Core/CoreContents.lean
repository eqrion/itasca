import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.Abs.Core.Typing

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Actual owned store shape supplies every non-function source payload typing
fact required by mutable scalar execution. -/
theorem decodeStore_contents_typed {M : Type} (view : M → Slice U8)
    (code : CodeInterpretation) (store : runtime.store.Store M)
    (shape : Shape view store) (sourceSyntax : StoreSyntax code store) (segments : SegmentBounds store) :
    Abs.StoreContentsTyped (decodeStore view code store) := by
  obtain ⟨globals,tables,memories,elements,data⟩ := decoded_components_typed view code store shape sourceSyntax segments
  exact ⟨globals,tables,memories,elements,data⟩

end Itasca.Runtime.Store
