import Itasca.Runtime.Store.Initialization.SegmentCounts
import Itasca.Runtime.Interp.Machine.Functions.Typing
import Itasca.Runtime.SourceMachine.Core
import Itasca.Runtime.SourceMachine.Float.Descriptor
import Itasca.Runtime.SourceMachine.Stateful.Descriptor
import Itasca.Runtime.Interp.Relations.CompiledFunctions
import Itasca.Runtime.Compiler.Local.Control.Function.CumulativeFunctionContext
import Itasca.Runtime.Integration.Execution.Ownership.Contents
import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Store.Invariant.FunctionTables
import Itasca.Runtime.Store.Invariant.CoreTypingExtension
import Itasca.Runtime.SourceMachine.ModuleBindingsExtension
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Integration.Execution.Ownership.StoreOperations
namespace Itasca.Runtime.Integration
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

end Itasca.Runtime.Integration
