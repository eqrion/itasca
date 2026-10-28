import Exec.Representation.StoreInvariant
import Exec.Store.Api.Grow
import Exec.Store.Invariant.ObjectExtension
import Exec.Interp.Memory.MemoryDecode
import Exec.Spec.MemoryGrowth
namespace Exec.Store
open Aeneas Aeneas.Std SpecExt

/-- A page-aligned natural byte count has the same rational page quotient used
by the generated memory-growth rule. -/
theorem memory_page_quotient (length : Nat) (aligned : length % 65536 = 0) :
    (length : Rat) / 65536 = ((length / 65536 : Nat) : Rat) := by
  have parts : length = length / 65536 * 65536 := by omega
  conv_lhs => rw [parts]
  push_cast
  ring

theorem decode_memory_growth {M : Type} (view : M → Slice U8)
    (old : runtime.store.MemInst M) (buffer : M) (delta : U32)
    (shape : MemoryShape view old)
    (values : (view buffer).val = (view old.buf).val ++ List.replicate (delta.val * 65536) 0#u8)
    (capacity : (view old.buf).length / 65536 + delta.val ≤ 65536)
    (maximum : (view old.buf).length / 65536 + delta.val ≤
      (core.option.Option.unwrap_or old.maximum 65536#u32).val) :
    fun_growmemory (decodeMemory view old) delta.val
      (some (decodeMemory view {old with buf := buffer})) := by
  have lengths : (view buffer).length = (view old.buf).length + delta.val * 65536 := by
    simpa only [List.length_append,List.length_replicate] using congrArg List.length values
  have pages : (view buffer).length / 65536 = (view old.buf).length / 65536 + delta.val := by omega
  have oldWf : wf_meminst (decodeMemory view old) := by
    apply wf_meminst.meminst_case_
    · apply wf_memtype.memtype_case_0
      exact decodeLimits_wf _ _ (by have bound := shape.2.1; scalar_tac)
    · exact decodeBytes_wf _
  have freshWf : wf_meminst (decodeMemory view {old with buf := buffer}) := by
    apply wf_meminst.meminst_case_
    · apply wf_memtype.memtype_case_0
      exact decodeLimits_wf _ _ (by change (view buffer).length / 65536 ≤ U32.max; rw [pages]; scalar_tac)
    · exact decodeBytes_wf _
  have bound : Forall (fun x => (((view old.buf).length / 65536 + delta.val : Nat) : Rat) ≤ (proj_uN_0 x : Rat))
      (Option.toList (old.maximum.map (fun x => uN.mk_uN x.val))) := by
    cases hm : old.maximum with
    | none => simp [Forall]
    | some mx =>
      intro x member
      simp only [Option.map_some,Option.toList_some,List.mem_singleton] at member
      subst x
      have : (view old.buf).length / 65536 + delta.val ≤ mx.val := by
        simpa only [hm,core.option.Option.unwrap_or] using maximum
      exact_mod_cast this
  have natValue : rat_to_nat (((view old.buf).length / 65536 + delta.val : Nat) : Rat) =
      (view old.buf).length / 65536 + delta.val := by
    simp only [rat_to_nat,Rat.num_natCast,Rat.den_natCast]
    change ((((((view old.buf).length / 65536 + delta.val) : Nat) : _root_.Int).tdiv 1).toNat) = _
    simp only [_root_.Int.tdiv_one,_root_.Int.toNat_natCast]
  have exactMemory : decodeMemory view {old with buf := buffer} =
      {TYPE := .PAGE (.mk_limits (.mk_uN (rat_to_nat (((view old.buf).length / 65536 + delta.val : Nat) : Rat)))
        (old.maximum.map (fun x => .mk_uN x.val))),
       BYTES := decodeBytes (view old.buf).val ++ List.replicate (delta.val * (64 * Ki)) (.mk_byte 0)} := by
    simp only [decodeMemory,decodeLimits_option,natValue,pages]
    simp [OMap,Function.comp_def,decodeBytes,values,List.map_append,List.map_replicate,Ki]
  apply fun_growmemory.fun_growmemory_case_0 _ _ _ (.mk_uN ((view old.buf).length / 65536))
    (old.maximum.map (fun x => .mk_uN x.val)) (decodeBytes (view old.buf).val)
    (((view old.buf).length / 65536 + delta.val : Nat) : Rat)
  · simp [decodeMemory,decodeLimits,OMap]
  · simp only [decodeBytes,List.length_map,Ki]
    norm_num
    rw [memory_page_quotient _ shape.1]
  · exact bound
  · norm_num
    exact_mod_cast capacity
  · exact exactMemory
  · exact freshWf
  · exact oldWf
  · rw [← exactMemory]
    exact freshWf
end Exec.Store
