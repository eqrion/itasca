import Exec.Store.Invariant.Typing
import Exec.Spec.Mutation
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Replacing memory contents while retaining its maximum and not shrinking
its byte buffer satisfies generated memory-instance extension. -/
theorem decodeMemory_extends {M : Type} (view : M → Slice U8)
    (before after : runtime.store.MemInst M)
    (maximum : after.maximum = before.maximum)
    (length : (view before.buf).length ≤ (view after.buf).length)
    (old : wf_meminst (decodeMemory view before))
    (fresh : wf_meminst (decodeMemory view after)) :
    Extend_meminst (decodeMemory view before) (decodeMemory view after) := by
  unfold decodeMemory at old fresh ⊢
  rw [maximum] at fresh ⊢
  simp only [decodeLimits_option] at old fresh ⊢
  exact .mk_Extend_meminst _ _ _ _ _ (Nat.div_le_div_right length)
    (by simpa only [decodeBytes, List.length_map] using length) old fresh

/-- Table contents may change and grow while preserving reference type and
maximum; the generated extension relation retains both endpoint wf premises. -/
theorem decodeTable_extends (before after : runtime.store.TableInst)
    (ty : after.ty = before.ty) (maximum : after.maximum = before.maximum)
    (length : before.elements.length ≤ after.elements.length)
    (old : wf_tableinst (decodeTable before)) (fresh : wf_tableinst (decodeTable after)) :
    Extend_tableinst (decodeTable before) (decodeTable after) := by
  unfold decodeTable at old fresh ⊢
  rw [ty, maximum] at fresh ⊢
  simp only [decodeLimits_option] at old fresh ⊢
  exact .mk_Extend_tableinst _ _ _ _ _ _ length
    (by simpa only [List.length_map] using length) old fresh
end Itasca.Runtime.Store
