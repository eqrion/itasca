import Itasca.Runtime.Interp.Simd.Memory.SimdMemoryRelation
import Itasca.Runtime.Interp.Memory.MemoryDecode
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt

/-- The structured byte effect decodes an actual opaque buffer replacement exactly. -/
theorem MemoryBufferChange.decoded {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M) (buffer : M) (sourceAfter : _root_.store)
    (moduleEq : ambient.MODULE = Store.decodeInstance store inst)
    (mapped : inst.memories.val[0]? = some address)
    (found : store.memories.val[address.index.val]? = some object)
    (change : MemoryBufferChange (Store.decodeStore view code store) ambient (view object.buf) (view buffer) sourceAfter) :
    Store.decodeStore view code {store with memories := store.memories.set address.index {object with buf := buffer}} = sourceAfter := by
  generalize bytesEq : view buffer = after at change
  cases change with
  | unchanged => exact memory_unchanged_decodes view code store address object buffer found bytesEq
  | write start payload after inside payloadWf written =>
    exact memory_write_decodes view code store inst ambient address object buffer start payload
      moduleEq mapped found inside (by rw [bytesEq]; exact written)
end Itasca.Runtime.Interp.Simd
