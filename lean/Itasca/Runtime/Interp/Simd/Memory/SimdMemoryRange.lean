import Itasca.Runtime.Interp.Simd.Memory.SimdMemoryBytes
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

/-- SIMD accesses use the scalar effective-address check against the whole memory. -/
@[step] theorem memory_range (memory : Slice U8) (address offset : U32) (size : Usize)
    (_small : size.val ≤ 16) :
    runtime.interp.memory.address address offset size (Slice.len memory)
      ⦃ result => MemoryAddressEffect address offset size (Slice.len memory) result ⦄ :=
  memory_address_effect address offset size (Slice.len memory)
end Itasca.Runtime.Interp.Simd
