import Exec.Store.Initialization.SegmentCounts
import Exec.Interp.Machines.Core.CoreFunctionTyping
import Exec.Abs.Core
import Exec.Abs.Float.Decode
import Exec.Abs.Stateful.Descriptor
import Exec.Interp.Relations.CompiledFunctions
import Exec.Code.Local.Control.Common.CumulativeFunctionContext
import Exec.Theorems.Composition.Core.CoreContents
import Exec.Representation.Collection
import Exec.Store.Invariant.FunctionTables
import Exec.Store.Invariant.CoreTypingExtension
import Exec.Abs.ModuleBindingsExtension
import Exec.Interp.Relations.FrameStoreMetadata
import Exec.Theorems.Composition.Stateful.StatefulOwnership
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
