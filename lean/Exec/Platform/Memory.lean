import Exec.Platform.Alloc
import Exec.Generated.Equations

namespace Itasca.Runtime.Platform
open Aeneas Aeneas.Std

/-- Laws for the actual extracted memory dictionary, relative to the bytes used
by the store decoder. No promise of successful allocation or growth is made. -/
structure MemoryLaws {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) : Prop where
  read : ∀ m, ops.bytes m = .ok (view m)
  write : ∀ m, ∃ back, ops.bytes_mut m = .ok (view m, back) ∧
    ∀ bytes, bytes.length = (view m).length → view (back bytes) = bytes
  create : ∀ n, ops.new_zeroed n ⦃ result =>
    ∀ m, result = some m → (view m).val = List.replicate n.val 0#u8 ⦄
  grow : ∀ m n, ops.grow m n ⦃ result =>
    if result.1 then (view m).length ≤ n.val ∧
      (view result.2).val = (view m).val ++
        List.replicate (n.val - (view m).length) 0#u8
    else view result.2 = view m ⦄

end Itasca.Runtime.Platform
