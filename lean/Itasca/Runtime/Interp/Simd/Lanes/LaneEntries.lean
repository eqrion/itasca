import Itasca.Runtime.Interp.Simd.Relations.LaneRelation

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
