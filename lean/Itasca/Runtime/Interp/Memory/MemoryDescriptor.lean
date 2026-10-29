import Itasca.Runtime.Interp.Memory.MemoryDispatch
import Itasca.Runtime.Interp.Memory.MemoryDecode
import Itasca.Runtime.Interp.Relations.PackedMemorySource
import Itasca.Runtime.SourceMachine.Memory.Descriptor

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt
open Itasca.Runtime.Store

/-- The abstract indexed widths and the independent source helper enumerate the
same legal packed instructions. No execution relation is assumed by this map. -/
def packed {ty : Inn} (width : Abs.Memory.PackedWidth ty) : Spec.PackedMemory :=
  match ty,width with
  | .I32,.byte => .i32x8
  | .I32,.half => .i32x16
  | .I64,.byte => .i64x8
  | .I64,.half => .i64x16
  | .I64,.word => .i64x32

theorem packed_bytes {ty : Inn} (width : Abs.Memory.PackedWidth ty) :
    (packed width).bytes = width.bits / 8 := by cases ty <;> cases width <;> rfl

def loadOpcode : Abs.Memory.Load → U16
  | .full ty => numericLoadOpcode ty
  | .packed _ width sign => PackedMemory.loadOpcode (packed width) sign

def storeOpcode : Abs.Memory.Store → U16
  | .full ty => numericStoreOpcode ty
  | .packed _ width => PackedMemory.storeOpcode (packed width)

theorem load_width (op : Abs.Memory.Load) : (scalarLoadWidth (loadOpcode op)).val = op.bytes := by
  cases op with
  | full ty => cases ty <;> rfl
  | packed ty width sign => exact (PackedMemory.load_width _ _).trans (packed_bytes width)

theorem store_width (op : Abs.Memory.Store) : (scalarStoreWidth (storeOpcode op)).val = op.bytes := by
  cases op with
  | full ty => cases ty <;> rfl
  | packed ty width => exact (PackedMemory.store_width _).trans (packed_bytes width)

end Itasca.Runtime.Interp.MemoryDescriptor
