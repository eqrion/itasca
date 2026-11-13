import Itasca.Runtime.Interp.Simd.Lanes.SplatSound
import Itasca.Runtime.Interp.Simd.Integer.CompareSigned
import Itasca.Runtime.Spec.Simd.CompareInteger
import SpecExt.Builtins.Examples

/-!
Sections, each formerly its own module: Extract, ReplacePacking, Replace, ShuffleBytes, Swizzle.
-/

/-! ## Extract -/

section

/-!
Lane extraction: scalar word calculations, lane iteration, packing and source correspondence. The final handler facts feed SIMD dispatch and machine execution; independently consumed primitives remain below this construction.
-/

/-! ## Simd Extract Runtime -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

def extractOpcode (ty : lanetype) : U32 :=
  match ty with
  | .I8 => 22#u32
  | .I16 => 25#u32
  | .I32 => 27#u32
  | .I64 => 29#u32
  | .F32 => 31#u32
  | .F64 => 33#u32

@[step] theorem extract_access (ty : lanetype) (index : U32) (a b : U128)
    (valid : index.val < 128/lsize ty) :
    runtime.interp.simd.access_lane (extractOpcode ty) index a b ⦃ result =>
      ∃ value, result = .Ok value ∧
        value.val = a.val / 2^(lsize ty*index.val) % 2^lsize ty ⦄ := by
  cases ty <;> unfold runtime.interp.simd.access_lane extractOpcode
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) ⦃ _ ⦄
  all_goals rw [bind_ok]
  all_goals step as ⟨count, countEq⟩
  all_goals norm_num [lsize, size, valtype_numtype, psize] at valid countEq
  all_goals have fits : ¬ index ≥ count := by scalar_tac
  all_goals rw [if_neg fits]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok false) _) ⦃ _ ⦄
  all_goals rw [bind_ok]
  all_goals simp only [Bool.false_eq_true, ite_false]
  all_goals step with lane as ⟨value, valueEq⟩
  all_goals simp only [lift, bind_ok]
  all_goals with_unfolding_all change (Result.ok _) ⦃ _ ⦄
  all_goals simp only [WP.spec_ok]
  all_goals refine ⟨_, rfl, ?_⟩
  all_goals simp only [UScalar.cast_val_eq]
  all_goals norm_num only [UScalar.size, UScalarTy.numBits]
  all_goals simp only [valueEq]
  all_goals norm_num [lsize, size, valtype_numtype, psize]
  all_goals omega

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Extract Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

theorem extract_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : lanetype) (offset laneIndex : U32) (bits a b c : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (extractOpcode ty) offset laneIndex bits a b c memory =
      Aeneas.Std.bind (runtime.interp.simd.access_lane (extractOpcode ty) laneIndex a b)
        (fun result => Result.ok (result, memory)) := by
  cases ty <;> unfold runtime.interp.simd.simd extractOpcode <;> with_unfolding_all rfl

end Itasca.Runtime.Interp.Simd

end

end

/-! ## ReplacePacking -/

section

/-!
Packed-vector effects of lane replacement.

Main declarations: `unpack_lanes_write` and `pack_lanes_write`. A direct consumer is `Interp.Simd.Lanes.Replace`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem unpack_lanes_write (ty : lanetype) (index : Nat) (v : BitVec 128) (x : BitVec 64)
    (valid : index < 128/lsize ty) :
    SpecExt.Builtins.unpackLanes ty (128/lsize ty) (writeLaneBits (lsize ty) index v x).toNat =
      (SpecExt.Builtins.unpackLanes ty (128/lsize ty) v.toNat).set index
        (SpecExt.Builtins.laneOfBits ty (x.setWidth (lsize ty)).toNat) := by
  apply List.ext_getElem?
  intro j
  rw [SpecExt.Builtins.unpackLanes_getElem?]
  by_cases inside : j < 128/lsize ty
  · have bound : j < (SpecExt.Builtins.unpackLanes ty (128/lsize ty) v.toNat).length := by
      simpa only [SpecExt.Builtins.unpackLanes_length] using inside
    by_cases same : j = index
    · subst j
      simp only [inside, if_true]
      rw [List.getElem?_set_self (by simpa [SpecExt.Builtins.unpackLanes_length] using valid)]
      rw [←lane_bits_to_nat, lane_bits_write_same _ _ _ _ (lane_range _ _ valid)]
    · rw [List.getElem?_set_ne (Ne.symm same), SpecExt.Builtins.unpackLanes_getElem?]
      simp only [inside, if_true]
      rw [←lane_bits_to_nat, lane_bits_write_other _ _ _ _ _ (lane_range _ _ inside) same, lane_bits_to_nat]
  · have outside : (SpecExt.Builtins.unpackLanes ty (128/lsize ty) v.toNat).length ≤ j := by
      simpa only [SpecExt.Builtins.unpackLanes_length] using Nat.le_of_not_gt inside
    simp only [inside, if_false]
    exact (List.getElem?_eq_none (by simpa only [List.length_set] using outside)).symm

theorem pack_lanes_write (ty : lanetype) (index : Nat) (v : BitVec 128) (x : BitVec 64)
    (valid : index < 128/lsize ty) :
    uN.mk_uN (writeLaneBits (lsize ty) index v x).toNat =
      inv_lanes_ (Spec.Simd.shapeOf ty)
        ((lanes_ (Spec.Simd.shapeOf ty) (.mk_uN v.toNat)).set index
          (SpecExt.Builtins.laneOfBits ty (x.setWidth (lsize ty)).toNat)) := by
  change uN.mk_uN _ = uN.mk_uN (SpecExt.Builtins.packLanes ty _)
  dsimp only [lanes_, Spec.Simd.shapeOf, proj_uN_0]
  rw [←unpack_lanes_write ty index v x valid, SpecExt.Builtins.pack_unpackLanes,
    Spec.Simd.shape_of_covers,
    Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le (by rfl))]

end Itasca.Runtime.Interp.Simd

end

/-! ## Replace -/

section

/-!
Lane replacement execution and source correspondence. Shared replacement packing remains below memory-lane stores.
-/

/-! ## Simd Replace Runtime -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

def replaceOpcode (ty : lanetype) : U32 :=
  match ty with
  | .I8 => 23#u32
  | .I16 => 26#u32
  | .I32 => 28#u32
  | .I64 => 30#u32
  | .F32 => 32#u32
  | .F64 => 34#u32

@[step] theorem replace_access (ty : lanetype) (index : U32) (a b : U128)
    (valid : index.val < 128/lsize ty) :
    runtime.interp.simd.access_lane (replaceOpcode ty) index a b ⦃ result =>
      ∃ value, result = .Ok value ∧
        value.bv = writeLaneBits (lsize ty) index.val a.bv (splatInput ty b).bv ⦄ := by
  cases ty <;> unfold runtime.interp.simd.access_lane replaceOpcode
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) ⦃ _ ⦄
  all_goals rw [bind_ok]
  all_goals step as ⟨count, countEq⟩
  all_goals norm_num [lsize, size, valtype_numtype, psize] at valid countEq
  all_goals have fits : ¬ index ≥ count := by scalar_tac
  all_goals rw [if_neg fits]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok true) _) ⦃ _ ⦄
  all_goals rw [bind_ok]
  all_goals simp only [ite_true, lift, bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) ⦃ _ ⦄
  all_goals rw [bind_ok]
  all_goals step with put as ⟨value, bits⟩
  all_goals first
    | exact ⟨value, rfl, bits⟩
    | (simp only [bind_ok, WP.spec_ok]; exact ⟨value, rfl, bits⟩)

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Replace Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

@[step] theorem replace_access_sound (ty : lanetype) (index : U32) (a b : U128)
    (valid : index.val < 128/lsize ty) :
    runtime.interp.simd.access_lane (replaceOpcode ty) index a b ⦃ result =>
      ∃ value, result = .Ok value ∧
        Step_pure [.VCONST .V128 (.mk_uN a.val),
          .CONST (unpack ty) (Spec.Simd.scalarInput ty (UScalar.cast .U64 b).bv),
          .VREPLACE_LANE (Spec.Simd.shapeOf ty) (.mk_uN index.val)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  apply WP.spec_mono (replace_access ty index a b valid)
  rintro result ⟨value, exactResult, bits⟩
  refine ⟨value, exactResult, ?_⟩
  have packed := (congrArg (fun (v : BitVec 128) => uN.mk_uN v.toNat) bits).trans
    (pack_lanes_write ty index.val a.bv (splatInput ty b).bv valid)
  have source := Spec.Simd.replace_step ty index.val a.bv value.bv (splatInput ty b).bv valid packed
  rw [splat_input_source] at source
  exact source

theorem replace_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : lanetype) (offset laneIndex : U32) (bits a b c : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (replaceOpcode ty) offset laneIndex bits a b c memory =
      Aeneas.Std.bind (runtime.interp.simd.access_lane (replaceOpcode ty) laneIndex a b)
        (fun result => Result.ok (result, memory)) := by
  cases ty <;> unfold runtime.interp.simd.simd replaceOpcode <;> with_unfolding_all rfl

@[step] theorem replace_dispatch_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : lanetype) (offset laneIndex : U32) (bits a b c : U128)
    (memory : Option (Slice U8)) (valid : laneIndex.val < 128/lsize ty) :
    runtime.interp.simd.simd floats (replaceOpcode ty) offset laneIndex bits a b c memory
      ⦃ result => ∃ value, result = (.Ok value, memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN a.val),
          .CONST (unpack ty) (Spec.Simd.scalarInput ty (UScalar.cast .U64 b).bv),
          .VREPLACE_LANE (Spec.Simd.shapeOf ty) (.mk_uN laneIndex.val)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [replace_dispatch_eq]
  step with replace_access_sound ty laneIndex a b valid as ⟨result, value, exactResult, source⟩
  exact ⟨value, by rw [exactResult], source⟩

end Itasca.Runtime.Interp.Simd

end

end

/-! ## ShuffleBytes -/

section

/-!
Byte selection and the shuffle/swizzle loop. Both operations consume this common byte calculation independently of their source correspondence.
-/

/-! ## Simd Shuffle Select -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

def selectedByte (shuffle : Bool) (x y : BitVec 128) (n : Nat) : BitVec 8 :=
  if n < 16 then laneBits 8 n x
  else if shuffle && decide (n < 32) then laneBits 8 (n-16) y else 0

@[step] theorem shuffle_select (op n : U32) (x y : U128) :
    (if n < 16#u32 then runtime.interp.simd.lane x 8#u32 n
      else if op = 13#u32 then
        if n < 32#u32 then do
          let index ← n - 16#u32
          runtime.interp.simd.lane y 8#u32 index
        else Result.ok 0#u64
      else Result.ok 0#u64)
      ⦃ value => value.bv.setWidth 8 = selectedByte (decide (op = 13#u32)) x.bv y.bv n.val ⦄ := by
  split
  · rename_i first
    have small : n.val < 16 := by scalar_tac
    step with lane as ⟨value,bits⟩
    simp only [selectedByte,if_pos small]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth]
    change value.val % 2^8 = _
    rw [bits,lane_bits_to_nat]
    simp
  · rename_i rest
    have large : ¬n.val < 16 := by scalar_tac
    split
    · rename_i shuffle
      split
      · rename_i second
        have small : n.val < 32 := by scalar_tac
        step as ⟨index,indexEq⟩
        step with lane as ⟨value,bits⟩
        simp only [selectedByte,if_neg large,shuffle,decide_true,Bool.true_and,decide_eq_true_eq,if_pos small]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth]
        change value.val % 2^8 = _
        rw [bits,lane_bits_to_nat]
        simp [indexEq]
      · rename_i outside
        have large32 : ¬n.val < 32 := by scalar_tac
        simp [selectedByte,large,shuffle,large32]
    · rename_i swizzle
      simp [selectedByte,large,swizzle]

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Shuffle Loop -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

def shuffleByte (op : U32) (bits x y : U128) (index : Nat) : BitVec 8 :=
  selectedByte (decide (op = 13#u32)) x.bv y.bv
    (laneBits 8 index (if op = 13#u32 then bits else y).bv).toNat

@[step] theorem shuffle_loop (op : U32) (bits x y initial : U128) (i : U32)
    (position : i.val ≤ 16)
    (initializedPrefix : ∀ j, j < i.val → laneBits 8 j initial.bv = shuffleByte op bits x y j) :
    runtime.interp.simd.shuffle_lanes_loop op bits x y initial i ⦃ result =>
      ∀ j, j < 16 → laneBits 8 j result.bv = shuffleByte op bits x y j ⦄ := by
  unfold runtime.interp.simd.shuffle_lanes_loop
  apply loop.spec_decr_nat (fun p => 16-p.2.val)
    (fun p => p.2.val ≤ 16 ∧ ∀ j, j < p.2.val → laneBits 8 j p.1.bv = shuffleByte op bits x y j)
  · rintro ⟨current,index⟩ ⟨indexBound,initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.shuffle_lanes_loop.body
    dsimp only
    split
    · rename_i more
      have less : index.val < 16 := by scalar_tac
      have choice : (if op = 13#u32 then Result.ok bits else Result.ok y) =
          Result.ok (if op = 13#u32 then bits else y) := by split <;> rfl
      rw [choice,bind_ok]
      step with lane as ⟨selector,selectorEq⟩
      have selectorBound : selector.val < 2^8 := by rw [selectorEq]; exact Nat.mod_lt _ (by decide)
      have selectorCast : (UScalar.cast .U32 selector).val =
          (laneBits 8 index.val (if op = 13#u32 then bits else y).bv).toNat := by
        rw [UScalar.cast_val_eq, Nat.mod_eq_of_lt (by scalar_tac)]
        rw [selectorEq,lane_bits_to_nat]
        rfl
      simp only [lift,bind_ok]
      step with shuffle_select as ⟨value,valueEq⟩
      rw [selectorCast] at valueEq
      have atIndex : value.bv.setWidth 8 = shuffleByte op bits x y index.val := valueEq
      step with put_lanes as ⟨updated,same,other⟩
      step as ⟨next,nextEq⟩
      refine ⟨?_,?_,?_⟩
      · omega
      · intro j bound
        by_cases eq : j = index.val
        · subst j; exact same.trans atIndex
        · exact (other j (by omega) eq).trans (initialized j (by omega))
      · omega
    · have finished : index.val = 16 := by scalar_tac
      simpa [finished] using initialized
  · exact ⟨position,initializedPrefix⟩

@[step] theorem shuffle_lanes (op : U32) (bits x y : U128) :
    runtime.interp.simd.shuffle_lanes op bits x y ⦃ result =>
      ∀ j, j < 16 → laneBits 8 j result.bv = shuffleByte op bits x y j ⦄ := by
  unfold runtime.interp.simd.shuffle_lanes
  exact shuffle_loop op bits x y 0#u128 0#u32 (by simp) (by simp)

end Itasca.Runtime.Interp.Simd

end

end

/-! ## Swizzle -/

section

/-!
Byte swizzle: scalar word calculations, lane iteration, packing and source correspondence. The final handler facts feed SIMD dispatch and machine execution; independently consumed primitives remain below this construction.
-/

/-! ## Simd Swizzle Packing -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem swizzle_byte_source (bits x y : U128) (j : Nat) :
    (shuffleByte 14#u32 bits x y j).toNat =
      proj_uN_0 ((Spec.Simd.swizzleWords x.bv)[Spec.Simd.byteAt y.bv j]!) := by
  change (selectedByte false x.bv y.bv (laneBits 8 j y.bv).toNat).toNat = _
  rw [lane_bits_to_nat]
  change (selectedByte false x.bv y.bv (Spec.Simd.byteAt y.bv j)).toNat = _
  rw [Spec.Simd.swizzle_words_get _ _ (Spec.Simd.byte_at_bound _ _)]
  by_cases first : Spec.Simd.byteAt y.bv j < 16
  · simp only [selectedByte,if_pos first]
    exact lane_bits_to_nat 8 _ x.bv
  · simp [selectedByte,first,proj_uN_0]

theorem swizzle_packed (bits x y result : U128)
    (lanes : ∀ j, j < 16 → laneBits 8 j result.bv = shuffleByte 14#u32 bits x y j) :
    uN.mk_uN result.val = inv_lanes_ (Spec.Simd.shapeOf .I8)
      ((List.range 16).map (fun k => lane_.mk_lane__0 .I8
        ((Spec.Simd.swizzleWords x.bv)[Spec.Simd.byteAt y.bv k]!))) := by
  let values := fun (k : Nat) => proj_uN_0 ((Spec.Simd.swizzleWords x.bv)[Spec.Simd.byteAt y.bv k]!)
  have selected (j : Nat) (valid : j < 16) :
      result.val/2^(lsize lanetype.I8*j)%2^lsize lanetype.I8 = values j := by
    change result.bv.toNat/2^(8*j)%2^8 = _
    rw [←lane_bits_to_nat,lanes j valid,swizzle_byte_source]
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

/-! ## Simd Swizzle Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem swizzle_lanes_sound (bits x y : U128) :
    runtime.interp.simd.shuffle_lanes 14#u32 bits x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        .VSWIZZLE Spec.Simd.byteShape] [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (shuffle_lanes 14#u32 bits x y)
  intro result lanes
  exact Spec.Simd.swizzle_step x.bv y.bv result.bv (swizzle_packed bits x y result lanes)

theorem swizzle_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats 14#u32 offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.shuffle_lanes 14#u32 bits x y)
        (fun value => Result.ok (.Ok value,memory)) := by
  unfold runtime.interp.simd.simd
  with_unfolding_all rfl

@[step] theorem swizzle_dispatch_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats 14#u32 offset laneIndex bits x y z memory ⦃ result =>
      ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
          .VSWIZZLE Spec.Simd.byteShape] [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [swizzle_dispatch_eq]
  step with swizzle_lanes_sound as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

end

end
