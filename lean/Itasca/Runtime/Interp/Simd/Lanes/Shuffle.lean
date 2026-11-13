import Itasca.Runtime.Interp.Simd.Relations.InputValues
import Itasca.Runtime.Interp.Simd.Lanes.Swizzle
import Itasca.Runtime.Spec.Simd.CompareInteger
import SpecExt.Builtins.Examples

/-!
Sections, each formerly its own module: LaneEntries, Shuffle.
-/

/-! ## LaneEntries -/

section

/-!
Source correspondence for SIMD lane opcode entries.

Main declarations: `lane_entry_21` and `lane_entry_sound`. A direct consumer is `Interp.Simd.Execution.LaneValuesExecute`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Wasm2.Simd

theorem lane_entry_21 {F : Type} (floats : runtime.platform.FloatOps F) : LaneEntrySound floats 21#u32 := by
  intro op meaning offset laneIndex bits x y z memory valid
  change some LaneOperation.i8x16ExtractS = some op at meaning
  cases meaning
  apply WP.spec_mono (extract_signed_dispatch_sound floats .I8 offset laneIndex bits x y z memory valid)
  rintro result ⟨value,returned,source⟩
  have bounded := Spec.pure_i32_bound source
  refine ⟨value,returned,?_,fun _ => bounded⟩
  unfold LaneSourceEffect laneResult
  simp only [LaneOperation.replace,LaneOperation.scalar,Spec.Simd.valueOfBits,valtype_numtype,
    Bool.false_eq_true,↓reduceIte,admininstr_val,BitVec.toNat_setWidth,UScalar.bv_toNat,Nat.mod_eq_of_lt bounded]
  with_unfolding_all exact source

theorem lane_entry_22 {F : Type} (floats : runtime.platform.FloatOps F) : LaneEntrySound floats 22#u32 := by
  intro op meaning offset laneIndex bits x y z memory valid
  change some LaneOperation.i8x16ExtractU = some op at meaning
  cases meaning
  apply WP.spec_mono (extract_dispatch_values floats .I8 offset laneIndex bits x y z memory valid)
  rintro result ⟨value,returned,source,bounded⟩
  refine ⟨value,returned,?_,fun _ => bounded⟩
  with_unfolding_all exact source

theorem lane_entry_23 {F : Type} (floats : runtime.platform.FloatOps F) : LaneEntrySound floats 23#u32 := by
  intro op meaning offset laneIndex bits x y z memory valid
  change some LaneOperation.i8x16Replace = some op at meaning
  cases meaning
  have h := replace_dispatch_sound floats .I8 offset laneIndex bits x y z memory valid
  simp only [Spec.Simd.scalarInput,UScalar.cast_bv_eq,UScalarTy.numBits,
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)] at h
  apply WP.spec_mono h
  rintro result ⟨value,returned,source⟩
  refine ⟨value,returned,?_,?_⟩
  · with_unfolding_all exact source
  · intro impossible
    contradiction

theorem lane_entry_24 {F : Type} (floats : runtime.platform.FloatOps F) : LaneEntrySound floats 24#u32 := by
  intro op meaning offset laneIndex bits x y z memory valid
  change some LaneOperation.i16x8ExtractS = some op at meaning
  cases meaning
  apply WP.spec_mono (extract_signed_dispatch_sound floats .I16 offset laneIndex bits x y z memory valid)
  rintro result ⟨value,returned,source⟩
  have bounded := Spec.pure_i32_bound source
  refine ⟨value,returned,?_,fun _ => bounded⟩
  unfold LaneSourceEffect laneResult
  simp only [LaneOperation.replace,LaneOperation.scalar,Spec.Simd.valueOfBits,valtype_numtype,
    Bool.false_eq_true,↓reduceIte,admininstr_val,BitVec.toNat_setWidth,UScalar.bv_toNat,Nat.mod_eq_of_lt bounded]
  with_unfolding_all exact source

theorem lane_entry_25 {F : Type} (floats : runtime.platform.FloatOps F) : LaneEntrySound floats 25#u32 := by
  intro op meaning offset laneIndex bits x y z memory valid
  change some LaneOperation.i16x8ExtractU = some op at meaning
  cases meaning
  apply WP.spec_mono (extract_dispatch_values floats .I16 offset laneIndex bits x y z memory valid)
  rintro result ⟨value,returned,source,bounded⟩
  refine ⟨value,returned,?_,fun _ => bounded⟩
  with_unfolding_all exact source

theorem lane_entry_26 {F : Type} (floats : runtime.platform.FloatOps F) : LaneEntrySound floats 26#u32 := by
  intro op meaning offset laneIndex bits x y z memory valid
  change some LaneOperation.i16x8Replace = some op at meaning
  cases meaning
  have h := replace_dispatch_sound floats .I16 offset laneIndex bits x y z memory valid
  simp only [Spec.Simd.scalarInput,UScalar.cast_bv_eq,UScalarTy.numBits,
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)] at h
  apply WP.spec_mono h
  rintro result ⟨value,returned,source⟩
  refine ⟨value,returned,?_,?_⟩
  · with_unfolding_all exact source
  · intro impossible
    contradiction

theorem lane_entry_27 {F : Type} (floats : runtime.platform.FloatOps F) : LaneEntrySound floats 27#u32 := by
  intro op meaning offset laneIndex bits x y z memory valid
  change some LaneOperation.i32x4Extract = some op at meaning
  cases meaning
  apply WP.spec_mono (extract_dispatch_values floats .I32 offset laneIndex bits x y z memory valid)
  rintro result ⟨value,returned,source,bounded⟩
  refine ⟨value,returned,?_,fun _ => bounded⟩
  with_unfolding_all exact source

theorem lane_entry_28 {F : Type} (floats : runtime.platform.FloatOps F) : LaneEntrySound floats 28#u32 := by
  intro op meaning offset laneIndex bits x y z memory valid
  change some LaneOperation.i32x4Replace = some op at meaning
  cases meaning
  have h := replace_dispatch_sound floats .I32 offset laneIndex bits x y z memory valid
  simp only [Spec.Simd.scalarInput,UScalar.cast_bv_eq,UScalarTy.numBits,
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)] at h
  apply WP.spec_mono h
  rintro result ⟨value,returned,source⟩
  refine ⟨value,returned,?_,?_⟩
  · with_unfolding_all exact source
  · intro impossible
    contradiction

theorem lane_entry_29 {F : Type} (floats : runtime.platform.FloatOps F) : LaneEntrySound floats 29#u32 := by
  intro op meaning offset laneIndex bits x y z memory valid
  change some LaneOperation.i64x2Extract = some op at meaning
  cases meaning
  apply WP.spec_mono (extract_dispatch_values floats .I64 offset laneIndex bits x y z memory valid)
  rintro result ⟨value,returned,source,bounded⟩
  refine ⟨value,returned,?_,fun _ => bounded⟩
  with_unfolding_all exact source

theorem lane_entry_30 {F : Type} (floats : runtime.platform.FloatOps F) : LaneEntrySound floats 30#u32 := by
  intro op meaning offset laneIndex bits x y z memory valid
  change some LaneOperation.i64x2Replace = some op at meaning
  cases meaning
  have h := replace_dispatch_sound floats .I64 offset laneIndex bits x y z memory valid
  apply WP.spec_mono h
  rintro result ⟨value,returned,source⟩
  refine ⟨value,returned,?_,?_⟩
  · with_unfolding_all exact source
  · intro impossible
    contradiction

theorem lane_entry_31 {F : Type} (floats : runtime.platform.FloatOps F) : LaneEntrySound floats 31#u32 := by
  intro op meaning offset laneIndex bits x y z memory valid
  change some LaneOperation.f32x4Extract = some op at meaning
  cases meaning
  apply WP.spec_mono (extract_dispatch_values floats .F32 offset laneIndex bits x y z memory valid)
  rintro result ⟨value,returned,source,bounded⟩
  refine ⟨value,returned,?_,fun _ => bounded⟩
  with_unfolding_all exact source

theorem lane_entry_32 {F : Type} (floats : runtime.platform.FloatOps F) : LaneEntrySound floats 32#u32 := by
  intro op meaning offset laneIndex bits x y z memory valid
  change some LaneOperation.f32x4Replace = some op at meaning
  cases meaning
  have h := replace_dispatch_sound floats .F32 offset laneIndex bits x y z memory valid
  simp only [Spec.Simd.scalarInput,UScalar.cast_bv_eq,UScalarTy.numBits,
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)] at h
  apply WP.spec_mono h
  rintro result ⟨value,returned,source⟩
  refine ⟨value,returned,?_,?_⟩
  · with_unfolding_all exact source
  · intro impossible
    contradiction

theorem lane_entry_33 {F : Type} (floats : runtime.platform.FloatOps F) : LaneEntrySound floats 33#u32 := by
  intro op meaning offset laneIndex bits x y z memory valid
  change some LaneOperation.f64x2Extract = some op at meaning
  cases meaning
  apply WP.spec_mono (extract_dispatch_values floats .F64 offset laneIndex bits x y z memory valid)
  rintro result ⟨value,returned,source,bounded⟩
  refine ⟨value,returned,?_,fun _ => bounded⟩
  with_unfolding_all exact source

theorem lane_entry_34 {F : Type} (floats : runtime.platform.FloatOps F) : LaneEntrySound floats 34#u32 := by
  intro op meaning offset laneIndex bits x y z memory valid
  change some LaneOperation.f64x2Replace = some op at meaning
  cases meaning
  have h := replace_dispatch_sound floats .F64 offset laneIndex bits x y z memory valid
  apply WP.spec_mono h
  rintro result ⟨value,returned,source⟩
  refine ⟨value,returned,?_,?_⟩
  · with_unfolding_all exact source
  · intro impossible
    contradiction
theorem lane_entry_sound {F : Type} (floats : runtime.platform.FloatOps F) (opcode : U32) :
    LaneEntrySound floats opcode := by
  intro op meaning offset laneIndex bits x y z memory valid
  have range : 21 ≤ opcode.val ∧ opcode.val ≤ 34 := by
    unfold laneMeaning at meaning
    split at meaning <;> first | contradiction | omega
  rcases range with ⟨lower,upper⟩
  generalize h : opcode.val = n at lower upper
  interval_cases n
  · have eq : opcode = 21#u32 := by scalar_tac
    subst opcode
    exact lane_entry_21 floats op meaning offset laneIndex bits x y z memory valid
  · have eq : opcode = 22#u32 := by scalar_tac
    subst opcode
    exact lane_entry_22 floats op meaning offset laneIndex bits x y z memory valid
  · have eq : opcode = 23#u32 := by scalar_tac
    subst opcode
    exact lane_entry_23 floats op meaning offset laneIndex bits x y z memory valid
  · have eq : opcode = 24#u32 := by scalar_tac
    subst opcode
    exact lane_entry_24 floats op meaning offset laneIndex bits x y z memory valid
  · have eq : opcode = 25#u32 := by scalar_tac
    subst opcode
    exact lane_entry_25 floats op meaning offset laneIndex bits x y z memory valid
  · have eq : opcode = 26#u32 := by scalar_tac
    subst opcode
    exact lane_entry_26 floats op meaning offset laneIndex bits x y z memory valid
  · have eq : opcode = 27#u32 := by scalar_tac
    subst opcode
    exact lane_entry_27 floats op meaning offset laneIndex bits x y z memory valid
  · have eq : opcode = 28#u32 := by scalar_tac
    subst opcode
    exact lane_entry_28 floats op meaning offset laneIndex bits x y z memory valid
  · have eq : opcode = 29#u32 := by scalar_tac
    subst opcode
    exact lane_entry_29 floats op meaning offset laneIndex bits x y z memory valid
  · have eq : opcode = 30#u32 := by scalar_tac
    subst opcode
    exact lane_entry_30 floats op meaning offset laneIndex bits x y z memory valid
  · have eq : opcode = 31#u32 := by scalar_tac
    subst opcode
    exact lane_entry_31 floats op meaning offset laneIndex bits x y z memory valid
  · have eq : opcode = 32#u32 := by scalar_tac
    subst opcode
    exact lane_entry_32 floats op meaning offset laneIndex bits x y z memory valid
  · have eq : opcode = 33#u32 := by scalar_tac
    subst opcode
    exact lane_entry_33 floats op meaning offset laneIndex bits x y z memory valid
  · have eq : opcode = 34#u32 := by scalar_tac
    subst opcode
    exact lane_entry_34 floats op meaning offset laneIndex bits x y z memory valid
end Itasca.Runtime.Interp.Simd

end

/-! ## Shuffle -/

section

/-!
Shuffle packing and source dispatch, above the shared shuffle/swizzle byte loop.
-/

/-! ## Simd Shuffle Packing -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem shuffle_byte_source (bits x y : U128) (j : Nat)
    (bounded : Spec.Simd.byteAt bits.bv j < 32) :
    (shuffleByte 13#u32 bits x y j).toNat =
      proj_uN_0 ((Spec.Simd.byteWords x.bv ++ Spec.Simd.byteWords y.bv)[Spec.Simd.byteAt bits.bv j]!) := by
  change (selectedByte true x.bv y.bv (laneBits 8 j bits.bv).toNat).toNat = _
  rw [lane_bits_to_nat]
  change (selectedByte true x.bv y.bv (Spec.Simd.byteAt bits.bv j)).toNat = _
  rw [Spec.Simd.byte_words_append_get _ _ _ bounded]
  by_cases first : Spec.Simd.byteAt bits.bv j < 16
  · simp only [selectedByte,if_pos first]
    exact lane_bits_to_nat 8 _ x.bv
  · simp only [selectedByte,if_neg first,Bool.true_and,decide_eq_true_eq,if_pos bounded]
    exact lane_bits_to_nat 8 _ y.bv

theorem shuffle_packed (bits x y result : U128)
    (bounded : ∀ j, j < 16 → Spec.Simd.byteAt bits.bv j < 32)
    (lanes : ∀ j, j < 16 → laneBits 8 j result.bv = shuffleByte 13#u32 bits x y j) :
    uN.mk_uN result.val = inv_lanes_ (Spec.Simd.shapeOf .I8)
      ((List.range 16).map (fun k => lane_.mk_lane__0 .I8
        ((Spec.Simd.byteWords x.bv ++ Spec.Simd.byteWords y.bv)[
          proj_uN_0 (Spec.Simd.byteWords bits.bv)[k]!]!))) := by
  let values := fun (k : Nat) => proj_uN_0 ((Spec.Simd.byteWords x.bv ++ Spec.Simd.byteWords y.bv)[
    proj_uN_0 (Spec.Simd.byteWords bits.bv)[k]!]!)
  have selected (j : Nat) (valid : j < 16) :
      result.val / 2^(lsize lanetype.I8*j) % 2^lsize lanetype.I8 = values j := by
    change result.bv.toNat / 2^(8*j) % 2^8 = _
    rw [←lane_bits_to_nat,lanes j valid,shuffle_byte_source bits x y j (bounded j valid)]
    dsimp only [values]
    rw [Spec.Simd.byte_words_get bits.bv j valid]
    rfl
  have packed := SpecExt.Builtins.pack_map_of_lanes .I8 16 result.val values selected
  have valueBound : result.val < 2^(lsize lanetype.I8*16) := by
    change result.val < 2^128
    exact result.bv.isLt
  rw [Nat.mod_eq_of_lt valueBound] at packed
  change uN.mk_uN result.val = uN.mk_uN _
  apply congrArg uN.mk_uN
  rw [←packed]
  apply congrArg (SpecExt.Builtins.packLanes .I8)
  apply List.map_congr_left
  intro j member
  change lane_.mk_lane__0 .I8 (.mk_uN (values j)) = _
  dsimp only [values]
  congr 1

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Shuffle Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem shuffle_lanes_sound (bits x y : U128)
    (bounded : ∀ j, j < 16 → Spec.Simd.byteAt bits.bv j < 32) :
    runtime.interp.simd.shuffle_lanes 13#u32 bits x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        .VSHUFFLE Spec.Simd.byteShape (Spec.Simd.byteWords bits.bv)] [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (shuffle_lanes 13#u32 bits x y)
  intro result lanes
  apply Spec.Simd.shuffle_step x.bv y.bv result.bv (Spec.Simd.byteWords bits.bv)
    (Spec.Simd.byte_words_length _) _ (shuffle_packed bits x y result bounded lanes)
  intro index member
  obtain ⟨j,valid,rfl⟩ := List.mem_map.mp member
  exact bounded j (List.mem_range.mp valid)

theorem shuffle_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats 13#u32 offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.shuffle_lanes 13#u32 bits x y)
        (fun value => Result.ok (.Ok value,memory)) := by
  unfold runtime.interp.simd.simd
  with_unfolding_all rfl

@[step] theorem shuffle_dispatch_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8))
    (bounded : ∀ j, j < 16 → Spec.Simd.byteAt bits.bv j < 32) :
    runtime.interp.simd.simd floats 13#u32 offset laneIndex bits x y z memory ⦃ result =>
      ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
          .VSHUFFLE Spec.Simd.byteShape (Spec.Simd.byteWords bits.bv)] [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [shuffle_dispatch_eq]
  step with shuffle_lanes_sound as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

end

end
