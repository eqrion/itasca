import Itasca.Runtime.Interp.Simd.Relations.PureRelation
import Itasca.Runtime.Interp.Simd.Lanes.Shuffle

/-!
Source-effect certificates for SIMD shuffle instructions.

Main declarations: `ShuffleSourceEffect` and `ShuffleEntrySound`. A direct consumer is `Interp.Simd.Execution.ShuffleValuesExecute`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Wasm2.Simd

theorem shuffle_byte_words (bits : BitVec 128) (low high : U64)
    (combined : bits.toNat = low.val+high.val*2^64) :
    Spec.Simd.byteWords bits = shuffleIndices low high := by
  apply List.ext_getElem?
  intro j
  have lowBound : low.val < 2^64 := by scalar_tac
  have highBound : high.val < 2^64 := by scalar_tac
  by_cases valid : j < 16
  · interval_cases j
    all_goals norm_num [Spec.Simd.byteWords,Spec.Simd.byteAt,shuffleIndices,unpackBytes,combined,Nat.div_div_eq_div_mul]
    all_goals omega
  · have left : (Spec.Simd.byteWords bits).length = 16 := Spec.Simd.byte_words_length _
    have right : (shuffleIndices low high).length = 16 := by simp [shuffleIndices,unpackBytes_length]
    rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]
end Itasca.Runtime.Interp.Simd
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Wasm2.Simd

def ShuffleSourceEffect (low high : U64) (x y z value : BitVec 128) : Prop :=
  Step_pure ((Spec.Simd.operandValues [.V128,.V128] x y z).map admininstr_val ++
    [admininstr_instr (shuffle low high)])
    [admininstr_val (Spec.Simd.valueOfBits .V128 value)]

def ShuffleEntrySound {F : Type} (floats : runtime.platform.FloatOps F) : Prop :=
  ∀ (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) (low high : U64),
    bits.val = low.val+high.val*2^64 →
    (∀ lane ∈ shuffleIndices low high,proj_uN_0 lane < 32) →
    runtime.interp.simd.simd floats 13#u32 offset laneIndex bits x y z memory
      ⦃ result => ∃ value,result = (.Ok value,memory) ∧ ShuffleSourceEffect low high x.bv y.bv z.bv value.bv ⦄

theorem shuffle_entry_sound {F : Type} (floats : runtime.platform.FloatOps F) : ShuffleEntrySound floats := by
  intro offset laneIndex bits x y z memory low high combined bounded
  have indices := shuffle_byte_words bits.bv low high combined
  have allowed : ∀ j,j < 16 → Spec.Simd.byteAt bits.bv j < 32 := by
    intro j valid
    have member : uN.mk_uN (Spec.Simd.byteAt bits.bv j) ∈ Spec.Simd.byteWords bits.bv := by
      exact List.mem_map.mpr ⟨j,List.mem_range.mpr valid,rfl⟩
    rw [indices] at member
    exact bounded _ member
  apply WP.spec_mono (shuffle_dispatch_sound floats offset laneIndex bits x y z memory allowed)
  rintro result ⟨value,returned,source⟩
  refine ⟨value,returned,?_⟩
  rw [indices] at source
  with_unfolding_all exact source
end Itasca.Runtime.Interp.Simd
