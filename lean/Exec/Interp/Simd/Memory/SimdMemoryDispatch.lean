import Exec.Interp.Simd.Memory.SimdMemoryPlain
import Exec.Interp.Simd.Memory.SimdMemoryFullStore
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std

theorem memory_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (op offset lane : U32) (bits x y z : U128) (bytes : Slice U8)
    (memoryOp : op.val ≤ 11 ∨ (84 ≤ op.val ∧ op.val ≤ 93)) :
    runtime.interp.simd.simd floats op offset lane bits x y z (some bytes) =
      Aeneas.Std.bind (runtime.interp.simd.memory_op op offset lane x y bytes)
        (fun out => .ok (out.1,some out.2)) := by
  unfold runtime.interp.simd.simd
  split
  · rfl
  · rename_i larger
    have lower : op ≥ 84#u32 := by scalar_tac
    have upper : op ≤ 93#u32 := by scalar_tac
    rw [if_pos lower,if_pos upper]
    rfl

@[step] theorem plain_load_simd {F : Type} (floats : runtime.platform.FloatOps F)
    (op : PlainLoad) (offset lane : U32) (bits address value z : U128) (bytes : Slice U8) :
    runtime.interp.simd.simd floats op.opcode offset lane bits address value z (some bytes)
      ⦃ out => ∃ result, out = (result.1,some result.2) ∧ PlainLoadEffect op offset address bytes result ⦄ := by
  rw [memory_simd_eq _ _ _ _ _ _ _ _ _ (by cases op <;> decide)]
  step with plain_load_effect op offset lane address value bytes as ⟨out,effect⟩
  exact ⟨out,rfl,rfl,effect⟩

@[step] theorem full_store_simd {F : Type} (floats : runtime.platform.FloatOps F)
    (offset lane : U32) (bits address value z : U128) (bytes : Slice U8) :
    runtime.interp.simd.simd floats 11#u32 offset lane bits address value z (some bytes)
      ⦃ out => ∃ result, out = (result.1,some result.2) ∧ FullStoreEffect offset address value bytes result ⦄ := by
  rw [memory_simd_eq _ _ _ _ _ _ _ _ _ (by decide)]
  step with full_store_effect offset lane address value bytes as ⟨out,effect⟩
  exact ⟨out,rfl,rfl,effect⟩
end Exec.Interp.Simd
