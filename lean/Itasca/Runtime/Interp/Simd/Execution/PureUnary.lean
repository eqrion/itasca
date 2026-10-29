import Itasca.Runtime.Interp.Simd.Relations.PureRelation
import Itasca.Runtime.Interp.Simd.Integer.UnarySound
import Itasca.Runtime.Interp.Simd.Integer.PopcountSound
import Itasca.Runtime.Interp.Simd.Integer.ShiftSound
import Itasca.Runtime.Interp.Simd.Lanes.SplatSound
import Itasca.Runtime.Interp.Simd.Integer.AllTrueSound
import Itasca.Runtime.Interp.Simd.Integer.BitmaskSound

/-!
Source correspondence of pure unary opcode entries.

Main declarations: `pure_entry_15` and `pure_entry_205`. A direct consumer is `Interp.Simd.Execution.PureSound`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem pure_entry_15 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 15#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure15 = some op at meaning
  cases meaning
  have h := splat_dispatch_sound floats .I8 offset laneIndex bits x y z memory
  simp only [Spec.Simd.scalarInput,UScalar.cast_bv_eq,UScalarTy.numBits,
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)] at h
  with_unfolding_all exact h

theorem pure_entry_16 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 16#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure16 = some op at meaning
  cases meaning
  have h := splat_dispatch_sound floats .I16 offset laneIndex bits x y z memory
  simp only [Spec.Simd.scalarInput,UScalar.cast_bv_eq,UScalarTy.numBits,
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)] at h
  with_unfolding_all exact h

theorem pure_entry_17 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 17#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure17 = some op at meaning
  cases meaning
  have h := splat_dispatch_sound floats .I32 offset laneIndex bits x y z memory
  simp only [Spec.Simd.scalarInput,UScalar.cast_bv_eq,UScalarTy.numBits,
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)] at h
  with_unfolding_all exact h

theorem pure_entry_18 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 18#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure18 = some op at meaning
  cases meaning
  with_unfolding_all exact splat_dispatch_sound floats .I64 offset laneIndex bits x y z memory

theorem pure_entry_19 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 19#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure19 = some op at meaning
  cases meaning
  have h := splat_dispatch_sound floats .F32 offset laneIndex bits x y z memory
  simp only [Spec.Simd.scalarInput,UScalar.cast_bv_eq,UScalarTy.numBits,
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)] at h
  with_unfolding_all exact h

theorem pure_entry_20 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 20#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure20 = some op at meaning
  cases meaning
  with_unfolding_all exact splat_dispatch_sound floats .F64 offset laneIndex bits x y z memory

theorem pure_entry_96 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 96#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure96 = some op at meaning
  cases meaning
  with_unfolding_all exact signed_unary_dispatch_sound floats .I8 .absolute offset laneIndex bits x y z memory

theorem pure_entry_97 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 97#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure97 = some op at meaning
  cases meaning
  with_unfolding_all exact signed_unary_dispatch_sound floats .I8 .negate offset laneIndex bits x y z memory

theorem pure_entry_98 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 98#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure98 = some op at meaning
  cases meaning
  with_unfolding_all exact popcount_dispatch_sound floats  offset laneIndex bits x y z memory

theorem pure_entry_99 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 99#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure99 = some op at meaning
  cases meaning
  change runtime.interp.simd.simd floats (unaryOpcode .I8 .allTrue) offset laneIndex bits x y z memory ⦃ _ ⦄
  rw [all_true_dispatch_eq]
  step with all_true_lanes_sound .I8 x as ⟨value,source⟩
  exact ⟨value,rfl,by with_unfolding_all exact source⟩

theorem pure_entry_100 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 100#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure100 = some op at meaning
  cases meaning
  change runtime.interp.simd.simd floats (unaryOpcode .I8 .bitmask) offset laneIndex bits x y z memory ⦃ _ ⦄
  rw [bitmask_dispatch_eq]
  step with bitmask_lanes_sound .I8 x as ⟨value,source⟩
  exact ⟨value,rfl,by with_unfolding_all exact source⟩

theorem pure_entry_107 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 107#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure107 = some op at meaning
  cases meaning
  with_unfolding_all exact shift_dispatch_sound floats .I8 .left offset laneIndex bits x y z memory

theorem pure_entry_108 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 108#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure108 = some op at meaning
  cases meaning
  with_unfolding_all exact shift_dispatch_sound floats .I8 .signedRight offset laneIndex bits x y z memory

theorem pure_entry_109 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 109#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure109 = some op at meaning
  cases meaning
  with_unfolding_all exact shift_dispatch_sound floats .I8 .unsignedRight offset laneIndex bits x y z memory

theorem pure_entry_128 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 128#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure128 = some op at meaning
  cases meaning
  with_unfolding_all exact signed_unary_dispatch_sound floats .I16 .absolute offset laneIndex bits x y z memory

theorem pure_entry_129 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 129#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure129 = some op at meaning
  cases meaning
  with_unfolding_all exact signed_unary_dispatch_sound floats .I16 .negate offset laneIndex bits x y z memory

theorem pure_entry_131 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 131#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure131 = some op at meaning
  cases meaning
  change runtime.interp.simd.simd floats (unaryOpcode .I16 .allTrue) offset laneIndex bits x y z memory ⦃ _ ⦄
  rw [all_true_dispatch_eq]
  step with all_true_lanes_sound .I16 x as ⟨value,source⟩
  exact ⟨value,rfl,by with_unfolding_all exact source⟩

theorem pure_entry_132 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 132#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure132 = some op at meaning
  cases meaning
  change runtime.interp.simd.simd floats (unaryOpcode .I16 .bitmask) offset laneIndex bits x y z memory ⦃ _ ⦄
  rw [bitmask_dispatch_eq]
  step with bitmask_lanes_sound .I16 x as ⟨value,source⟩
  exact ⟨value,rfl,by with_unfolding_all exact source⟩

theorem pure_entry_139 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 139#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure139 = some op at meaning
  cases meaning
  with_unfolding_all exact shift_dispatch_sound floats .I16 .left offset laneIndex bits x y z memory

theorem pure_entry_140 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 140#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure140 = some op at meaning
  cases meaning
  with_unfolding_all exact shift_dispatch_sound floats .I16 .signedRight offset laneIndex bits x y z memory

theorem pure_entry_141 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 141#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure141 = some op at meaning
  cases meaning
  with_unfolding_all exact shift_dispatch_sound floats .I16 .unsignedRight offset laneIndex bits x y z memory

theorem pure_entry_160 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 160#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure160 = some op at meaning
  cases meaning
  with_unfolding_all exact signed_unary_dispatch_sound floats .I32 .absolute offset laneIndex bits x y z memory

theorem pure_entry_161 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 161#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure161 = some op at meaning
  cases meaning
  with_unfolding_all exact signed_unary_dispatch_sound floats .I32 .negate offset laneIndex bits x y z memory

theorem pure_entry_163 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 163#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure163 = some op at meaning
  cases meaning
  change runtime.interp.simd.simd floats (unaryOpcode .I32 .allTrue) offset laneIndex bits x y z memory ⦃ _ ⦄
  rw [all_true_dispatch_eq]
  step with all_true_lanes_sound .I32 x as ⟨value,source⟩
  exact ⟨value,rfl,by with_unfolding_all exact source⟩

theorem pure_entry_164 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 164#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure164 = some op at meaning
  cases meaning
  change runtime.interp.simd.simd floats (unaryOpcode .I32 .bitmask) offset laneIndex bits x y z memory ⦃ _ ⦄
  rw [bitmask_dispatch_eq]
  step with bitmask_lanes_sound .I32 x as ⟨value,source⟩
  exact ⟨value,rfl,by with_unfolding_all exact source⟩

theorem pure_entry_171 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 171#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure171 = some op at meaning
  cases meaning
  with_unfolding_all exact shift_dispatch_sound floats .I32 .left offset laneIndex bits x y z memory

theorem pure_entry_172 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 172#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure172 = some op at meaning
  cases meaning
  with_unfolding_all exact shift_dispatch_sound floats .I32 .signedRight offset laneIndex bits x y z memory

theorem pure_entry_173 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 173#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure173 = some op at meaning
  cases meaning
  with_unfolding_all exact shift_dispatch_sound floats .I32 .unsignedRight offset laneIndex bits x y z memory

theorem pure_entry_192 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 192#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure192 = some op at meaning
  cases meaning
  with_unfolding_all exact signed_unary_dispatch_sound floats .I64 .absolute offset laneIndex bits x y z memory

theorem pure_entry_193 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 193#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure193 = some op at meaning
  cases meaning
  with_unfolding_all exact signed_unary_dispatch_sound floats .I64 .negate offset laneIndex bits x y z memory

theorem pure_entry_195 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 195#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure195 = some op at meaning
  cases meaning
  change runtime.interp.simd.simd floats (unaryOpcode .I64 .allTrue) offset laneIndex bits x y z memory ⦃ _ ⦄
  rw [all_true_dispatch_eq]
  step with all_true_lanes_sound .I64 x as ⟨value,source⟩
  exact ⟨value,rfl,by with_unfolding_all exact source⟩

theorem pure_entry_196 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 196#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure196 = some op at meaning
  cases meaning
  change runtime.interp.simd.simd floats (unaryOpcode .I64 .bitmask) offset laneIndex bits x y z memory ⦃ _ ⦄
  rw [bitmask_dispatch_eq]
  step with bitmask_lanes_sound .I64 x as ⟨value,source⟩
  exact ⟨value,rfl,by with_unfolding_all exact source⟩

theorem pure_entry_203 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 203#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure203 = some op at meaning
  cases meaning
  with_unfolding_all exact shift_dispatch_sound floats .I64 .left offset laneIndex bits x y z memory

theorem pure_entry_204 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 204#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure204 = some op at meaning
  cases meaning
  with_unfolding_all exact shift_dispatch_sound floats .I64 .signedRight offset laneIndex bits x y z memory

theorem pure_entry_205 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 205#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure205 = some op at meaning
  cases meaning
  with_unfolding_all exact shift_dispatch_sound floats .I64 .unsignedRight offset laneIndex bits x y z memory

end Itasca.Runtime.Interp.Simd
