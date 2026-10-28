import Itasca.Runtime.Store.Initialization.SegmentCounts
import Itasca.Runtime.Interp.Machines.Core.CoreFunctionTyping
import Itasca.Runtime.Abs.Core
import Itasca.Runtime.Abs.Float.Decode
import Itasca.Runtime.Abs.Stateful.Descriptor
import Itasca.Runtime.Interp.Relations.CompiledFunctions
import Itasca.Runtime.Code.Local.Control.Common.CumulativeFunctionContext
import Itasca.Runtime.Theorems.Composition.Core.CoreContents
import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Store.Invariant.FunctionTables
import Itasca.Runtime.Store.Invariant.CoreTypingExtension
import Itasca.Runtime.Abs.ModuleBindingsExtension
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Theorems.Composition.Stateful.StatefulOwnership
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std

/-- An internal dispatch witness, established from exact runtime mutation
footprints. Segment contents may change; their checked bounds remain explicit. -/
structure CumulativeStoreMutation {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (before after : runtime.store.Store M) : Prop where
  metadata : Interp.FrameStoreMetadata before after
  externs : after.externs = before.externs
  shape : Store.Shape view after
  segmentBounds : Store.SegmentBounds after
  extension : Extend_store (Store.decodeStore view code before) (Store.decodeStore view code after)
  segmentCounts : Store.SegmentCounts before after
  limits : after.limits = before.limits

theorem CumulativeStoreMutation.ownership_bounds {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {before after : runtime.store.Store M}
    (mutation : CumulativeStoreMutation view code before after) :
    Store.ownershipBounds after = Store.ownershipBounds before := by
  unfold Store.ownershipBounds
  rw [mutation.metadata.functions,mutation.externs]

end Itasca.Runtime.Theorems
