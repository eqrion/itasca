import Itasca.Runtime.Spec.FloatTrunc
import Itasca.Runtime.Spec.Simd.CompareInteger
import Itasca.Runtime.Spec.FloatPromote
import Itasca.Runtime.Spec.Simd.ExtendLanes
import SpecExt.Builtins.Float.Sign

/-!
Sections, each formerly its own module: MemoryLoad, MemoryChunks, MemoryLane, MemoryExtend, MemoryLaneStore, MemorySplat, MemoryStore, MemoryZero, FloatUnary, FloatResize.
-/

/-! ## MemoryLoad -/

section

/-!
The source result relation for full-vector loads.

Main declarations: `fullLoadResult`. A direct consumer is `Spec.Simd.MemoryLane`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt SpecExt.Builtins

def fullLoadResult (bytes : List byte) (start : Nat) : List admininstr :=
  if start + 16 ≤ bytes.length then [.VCONST .V128 (inv_vbytes_ .V128 ((bytes.drop start).take 16))]
  else [.TRAP]

theorem vector_bytes_roundtrip (bytes : List byte) (valid : Forall wf_byte bytes)
    (sized : bytes.length = 16) : vbytes_ .V128 (inv_vbytes_ .V128 bytes) = bytes := by
  have roundtrip := integer_bytes_of_bytes bytes valid
  simpa [vbytes_,inv_vbytes_,ibytes_,inv_ibytes_,vsize,proj_uN_0,sized] using roundtrip

theorem vector_bytes_wf (bytes : List byte) (valid : Forall wf_byte bytes)
    (sized : bytes.length = 16) : wf_admininstr (.VCONST .V128 (inv_vbytes_ .V128 bytes)) := by
  have bounded := integer_of_bytes_bound bytes valid
  apply wf_admininstr.admininstr_case_20 _ _ (by decide)
  apply unsigned_wf_of_lt
  rw [sized] at bounded
  simpa [inv_vbytes_,inv_ibytes_,vsize,size,valtype_vectype] using bounded

theorem full_load_step (s : store) (f : frame) (argument : memarg) (address : Nat)
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.VLOAD .V128 none argument))
    (bytesWf : Forall wf_byte (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,.VLOAD .V128 none argument]⟩ []
      ⟨⟨s,f⟩,fullLoadResult (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES
        (address + proj_uN_0 argument.OFFSET)⟩ := by
  have byteCount : rat_to_nat ((Option.get! (size valtype.V128) : Rat) / 8) = 16 := by
    norm_num [size,rat_to_nat]
    rfl
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr [Segment.i32 address,.VLOAD .V128 none argument] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact operationWf)
  unfold fullLoadResult
  split
  · rename_i fits
    let bytes := (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES
    let start := address + proj_uN_0 argument.OFFSET
    have payloadWf : Forall wf_byte ((bytes.drop start).take 16) := by
      intro byte member
      exact bytesWf byte (List.mem_of_mem_drop (List.mem_of_mem_take member))
    have payloadLength : ((bytes.drop start).take 16).length = 16 := by
      simp only [List.length_take,List.length_drop]
      dsimp only [bytes,start]
      omega
    have valueWf := vector_bytes_wf _ payloadWf payloadLength
    have output := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [.VCONST .V128 (inv_vbytes_ .V128 ((bytes.drop start).take 16))] from by
      simpa [Forall] using valueWf)
    apply StepH.step
    apply Step.read _ _ _ ?_ input output
    apply Step_read.vload_val
    · simp [proj_num__0]
    · decide
    · simpa only [byteCount,proj_num__0,proj_uN_0,Option.get!_some,bytes,start] using
        vector_bytes_roundtrip _ payloadWf payloadLength
    · exact input
    · exact valueWf
    · exact Segment.index_wf 0 (by norm_num)
  · rename_i outside
    apply StepH.step
    apply Step.read _ _ _ ?_ input (wf_config_trap storeWf frameWf)
    apply Step_read.vload_oob
    · simp [proj_num__0]
    · decide
    · simpa only [byteCount,proj_num__0,proj_uN_0,Option.get!_some] using Nat.lt_of_not_ge outside
    · exact input
    · exact .admininstr_case_73
    · exact Segment.index_wf 0 (by norm_num)
end Itasca.Runtime.Spec.Simd

end

/-! ## MemoryChunks -/

section

/-!
Byte slices used by vector memory loads.

Main declarations: `integer_bytes_take` and `integer_bytes_chunk`. A direct consumer is `Spec.Simd.MemoryExtend`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem integer_bytes_take (count total value : Nat) (le : count ≤ total) :
    (integerBytes total value).take count = integerBytes count value := by
  induction count generalizing total value with
  | zero => simp [integerBytes]
  | succ count ih =>
    cases total with
    | zero => omega
    | succ total =>
      simpa only [integerBytes,List.take_succ_cons] using
        congrArg (List.cons (.mk_byte (value%256))) (ih total (value/256) (by omega))

theorem integer_bytes_drop (start total value : Nat) (le : start ≤ total) :
    (integerBytes total value).drop start = integerBytes (total-start) (value/256^start) := by
  induction start generalizing total value with
  | zero => simp
  | succ start ih =>
    cases total with
    | zero => omega
    | succ total =>
      simp only [integerBytes,List.drop_succ_cons]
      rw [ih total (value/256) (by omega)]
      simp only [Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm 256,Nat.add_sub_add_right]

theorem integer_bytes_chunk (width index value : Nat) (fit : index*width+width ≤ 8) :
    (integerBytes 8 value |>.drop (index*width) |>.take width) =
      integerBytes width ((value/256^(index*width))%256^width) := by
  rw [integer_bytes_drop _ _ _ (by omega),integer_bytes_take _ _ _ (by omega),integer_bytes_mod]
end Itasca.Runtime.Spec.Simd

end

/-! ## MemoryLane -/

section

/-!
Byte widths and source behavior of vector lane loads.

Main declarations: `lane_byte_count` and `lane_load_trap`. A direct consumer is `Spec.Simd.MemoryExtend`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt SpecExt.Builtins

theorem lane_byte_count (ty : Jnn) :
    rat_to_nat ((lsize (lanetype_Jnn ty) : Rat)/8) = lsize (lanetype_Jnn ty)/8 := by
  cases ty <;> norm_num [lsize,lanetype_Jnn,rat_to_nat,size,valtype_numtype,psize] <;> rfl

theorem lane_dimension (ty : Jnn) :
    ((128/lsize (lanetype_Jnn ty) : Nat) : Rat) = (128 : Rat)/lsize (lanetype_Jnn ty) := by
  cases ty <;> norm_num [lsize,lanetype_Jnn,size,valtype_numtype,psize]

theorem lane_load_value (ty : Jnn) (s : store) (f : frame) (argument : memarg) (address index : Nat)
    (before result : BitVec 128) (word : BitVec (lsize (lanetype_Jnn ty)))
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.VLOAD_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)))
    (bytesEq : ibytes_ (lsize (lanetype_Jnn ty)) (.mk_uN word.toNat) =
      ((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.drop (address+proj_uN_0 argument.OFFSET)).take (lsize (lanetype_Jnn ty)/8))
    (packed : uN.mk_uN result.toNat = inv_lanes_ (shapeOf (lanetype_Jnn ty))
      ((lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN before.toNat)).set index (.mk_lane__0 ty (.mk_uN word.toNat)))) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,.VCONST .V128 (.mk_uN before.toNat),
      .VLOAD_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)]⟩ []
      ⟨⟨s,f⟩,[.VCONST .V128 (.mk_uN result.toNat)]⟩ := by
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [Segment.i32 address,.VCONST .V128 (.mk_uN before.toNat),
        .VLOAD_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact const_wf before
    · exact operationWf)
  have output := wf_config_make storeWf frameWf (show Forall wf_admininstr [.VCONST .V128 (.mk_uN result.toNat)] from by
    simpa [Forall] using const_wf result)
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  apply Step_read.vload_lane_val _ _ _ _ _ _ _ (.mk_uN word.toNat) ty (128/lsize (lanetype_Jnn ty))
  · simp [proj_num__0]
  · simpa only [lane_byte_count,proj_num__0,proj_uN_0,Option.get!_some] using bytesEq
  · cases ty <;> rfl
  · exact lane_dimension ty
  · simpa only [shapeOf,List.modify_eq_set,proj_uN_0] using packed
  · exact input
  · exact const_wf result
  · exact Segment.index_wf 0 (by norm_num)
  · exact shape_of_wf _
  · cases ty <;> exact lane_of_bits_wf _ word.toNat word.isLt

theorem lane_load_trap (ty : Jnn) (s : store) (f : frame) (argument : memarg) (address index : Nat)
    (before : BitVec 128) (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.VLOAD_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)))
    (outside : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length < address+proj_uN_0 argument.OFFSET+lsize (lanetype_Jnn ty)/8) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,.VCONST .V128 (.mk_uN before.toNat),
      .VLOAD_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)]⟩ [] ⟨⟨s,f⟩,[.TRAP]⟩ := by
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [Segment.i32 address,.VCONST .V128 (.mk_uN before.toNat),
        .VLOAD_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact const_wf before
    · exact operationWf)
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_trap storeWf frameWf)
  apply Step_read.vload_lane_oob
  · simp [proj_num__0]
  · simpa only [lane_byte_count,proj_num__0,proj_uN_0,Option.get!_some] using outside
  · exact input
  · exact .admininstr_case_73
  · exact Segment.index_wf 0 (by norm_num)
end Itasca.Runtime.Spec.Simd

end

/-! ## MemoryExtend -/

section

/-!
The source operation for widening vector loads.

Main declarations: `memoryExtendSource`. A direct consumer is `Integration.Api.InvocationResourcesAdequate`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt SpecExt.Builtins

def memoryExtendSource (ty : WidenWidth) (signed : Bool) (argument : memarg) : admininstr :=
  .VLOAD .V128 (some (.SHAPEX_ (.mk_sz ty.width) ty.count (widenSign signed))) argument

theorem memory_extend_byte_count (ty : WidenWidth) : rat_to_nat ((ty.width : Rat)*(ty.count : Rat)/8) = 8 := by
  cases ty <;> norm_num [WidenWidth.width,WidenWidth.input,WidenWidth.count,lsize,lanetype_Jnn,size,valtype_numtype,psize,rat_to_nat] <;> rfl

theorem memory_extend_bytes (ty : WidenWidth) : rat_to_nat ((ty.width : Rat)/8) = ty.width/8 := by
  cases ty <;> norm_num [WidenWidth.width,WidenWidth.input,lsize,lanetype_Jnn,size,valtype_numtype,psize,rat_to_nat] <;> rfl

theorem memory_extend_offset (ty : WidenWidth) (j : Nat) : rat_to_nat ((j : Rat)*(ty.width : Rat)/8) = j*(ty.width/8) := by
  have eq : ((j*ty.width : Nat) : Rat)/8 = ((j*(ty.width/8) : Nat) : Rat) := by
    cases ty <;> norm_num [WidenWidth.width,WidenWidth.input,lsize,lanetype_Jnn,size,valtype_numtype,psize] <;> ring
  rw [←Nat.cast_mul,eq]
  simp only [rat_to_nat,Rat.num_natCast,Rat.den_natCast]
  generalize j*(ty.width/8) = n
  change ((n:Int).tdiv (1:Int)).toNat = n
  simp only [Int.tdiv_one,Int.toNat_natCast]

theorem extend_load_value (ty : WidenWidth) (signed : Bool) (s : store) (f : frame) (argument : memarg)
    (address : Nat) (loaded result : BitVec 128)
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (memoryExtendSource ty signed argument))
    (bytesEq : ∀ j, j < ty.count → ibytes_ ty.width (.mk_uN (laneWord (lanetype_Jnn ty.input) loaded j).toNat) =
      ((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.drop (address+proj_uN_0 argument.OFFSET+j*(ty.width/8))).take (ty.width/8))
    (packed : uN.mk_uN result.toNat = widenResult ty false false signed loaded loaded) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,memoryExtendSource ty signed argument]⟩ []
      ⟨⟨s,f⟩,[.VCONST .V128 (.mk_uN result.toNat)]⟩ := by
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr [Segment.i32 address,memoryExtendSource ty signed argument] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact operationWf)
  have output := wf_config_make storeWf frameWf (show Forall wf_admininstr [.VCONST .V128 (.mk_uN result.toNat)] from by
    simpa [Forall] using const_wf result)
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  apply Step_read.vload_shape_val _ _ _ _ _ _ _ ((List.range ty.count).map
    (fun j => .mk_uN (laneWord (lanetype_Jnn ty.input) loaded j).toNat)) ty.output
  · intro j member;simp [proj_num__0]
  · have relation := forall2_map (List.range ty.count) id
      (fun j => uN.mk_uN (laneWord (lanetype_Jnn ty.input) loaded j).toNat)
      (fun j word => ibytes_ ty.width word =
        ((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.drop (address+proj_uN_0 argument.OFFSET+j*(ty.width/8))).take (ty.width/8))
      (by
        intro j member
        simpa only [id_eq,memory_extend_bytes,memory_extend_offset,proj_num__0,proj_uN_0,Option.get!_some] using bytesEq j (List.mem_range.mp member))
    simpa only [List.map_id_fun,id_eq,memory_extend_bytes,memory_extend_offset,proj_num__0,proj_uN_0,Option.get!_some] using relation
  · intro word member
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp member
    exact (laneWord (lanetype_Jnn ty.input) loaded index).isLt
  · cases ty <;> rfl
  · rw [packed]
    unfold widenResult widenWords Map
    simp only [List.map_map]
    congr 1
    · cases ty <;> rfl
    · apply List.map_congr_left
      intro j member
      simp only [widenBits,Bool.false_eq_true,↓reduceIte,Nat.add_zero]
      have ex := extend_bits_source (ty.width*2) signed (laneWord (lanetype_Jnn ty.input) loaded j) (by cases ty <;> decide)
      cases ty <;> exact congrArg (lane_.mk_lane__0 _) ex
  · exact input
  · exact const_wf result
  · exact Segment.index_wf 0 (by norm_num)
  · cases ty <;> exact shape_of_wf _
  · intro word member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    have ex := extend_bits_source (ty.width*2) signed (laneWord (lanetype_Jnn ty.input) loaded j) (by cases ty <;> decide)
    have bounded := unsigned_wf_of_lt (ty.width*2) (extendBits signed (ty.width*2) (laneWord (lanetype_Jnn ty.input) loaded j)).toNat (BitVec.isLt _)
    have wf : wf_uN (ty.width*2) (extend__ ty.width (ty.width*2) (widenSign signed)
        (.mk_uN (laneWord (lanetype_Jnn ty.input) loaded j).toNat)) := by
      change wf_uN (ty.width*2) (extend__ (lsize (lanetype_Jnn ty.input)) (ty.width*2) (if signed then .S else .U) _)
      rw [←ex];exact bounded
    cases ty <;> exact .lane__case_0 _ _ _ wf rfl
  · simp
end Itasca.Runtime.Spec.Simd
namespace Itasca.Runtime.Spec.Simd
open SpecExt SpecExt.Builtins

theorem extend_load_trap (ty : WidenWidth) (signed : Bool) (s : store) (f : frame) (argument : memarg)
    (address : Nat) (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (memoryExtendSource ty signed argument))
    (outside : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length < address+proj_uN_0 argument.OFFSET+8) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,memoryExtendSource ty signed argument]⟩ [] ⟨⟨s,f⟩,[.TRAP]⟩ := by
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr [Segment.i32 address,memoryExtendSource ty signed argument] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact operationWf)
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_trap storeWf frameWf)
  apply Step_read.vload_shape_oob
  · simp [proj_num__0]
  · simpa only [memory_extend_byte_count,proj_num__0,proj_uN_0,Option.get!_some] using outside
  · exact input
  · exact .admininstr_case_73
  · exact Segment.index_wf 0 (by norm_num)
end Itasca.Runtime.Spec.Simd

end

/-! ## MemoryLaneStore -/

section

/-!
Source reduction for bounded vector lane stores.

Main declarations: `lane_store_step`. A direct consumer is `Interp.Simd.Memory.LaneStoreSource`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt SpecExt.Builtins

theorem lane_store_step (ty : Jnn) (s : store) (f : frame) (argument : memarg) (address index : Nat)
    (before : BitVec 128) (word : BitVec (lsize (lanetype_Jnn ty)))
    (valid : index < 128/lsize (lanetype_Jnn ty))
    (selected : (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN before.toNat))[index]! = .mk_lane__0 ty (.mk_uN word.toNat))
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.VSTORE_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)))
    (mapped : 0 < f.MODULE.MEMS.length) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,.VCONST .V128 (.mk_uN before.toNat),
      .VSTORE_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)]⟩ []
      (if address+proj_uN_0 argument.OFFSET+lsize (lanetype_Jnn ty)/8 ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length then
        ⟨⟨memoryPayloadWrite s f (address+proj_uN_0 argument.OFFSET)
          (integerBytes (lsize (lanetype_Jnn ty)/8) word.toNat),f⟩,[]⟩
      else ⟨⟨s,f⟩,[.TRAP]⟩) := by
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [Segment.i32 address,.VCONST .V128 (.mk_uN before.toNat),
        .VSTORE_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact const_wf before
    · exact operationWf)
  split
  · rename_i inside
    have updatedWf := memory_payload_write_wf s f (address+proj_uN_0 argument.OFFSET)
      (integerBytes (lsize (lanetype_Jnn ty)/8) word.toNat) storeWf (integer_bytes_wf _ _)
    apply StepH.step
    apply Step.vstore_lane_val _ _ _ _ _ _ _ ty (128/lsize (lanetype_Jnn ty))
    · simp [proj_num__0]
    · simpa only [lane_byte_count,proj_num__0,proj_uN_0,Option.get!_some,memoryPayloadWrite] using
        fun_with_mem.fun_with_mem_case_0 s f (.mk_uN 0) (address+proj_uN_0 argument.OFFSET)
          (lsize (lanetype_Jnn ty)/8) (integerBytes (lsize (lanetype_Jnn ty)/8) word.toNat) mapped inside
          (.state_case_0 _ _ updatedWf frameWf) (.state_case_0 _ _ storeWf frameWf)
    · simpa only [lane_byte_count,proj_num__0,proj_uN_0,Option.get!_some] using inside
    · cases ty <;> rfl
    · exact lane_dimension ty
    · change proj_lane__0 ((lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN before.toNat))[index]!) ≠ none
      rw [selected]; simp [proj_lane__0]
    · simpa [lanes_,shapeOf,proj_uN_0,unpackLanes_length] using valid
    · change integerBytes (lsize (lanetype_Jnn ty)/8) word.toNat =
        ibytes_ (lsize (lanetype_Jnn ty)) (.mk_uN (proj_uN_0 (Option.get! (proj_lane__0
          ((lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN before.toNat))[index]!)))))
      rw [selected]
      rfl
    · exact input
    · exact wf_config_make updatedWf frameWf (forall_nil _)
    · exact Segment.index_wf 0 (by norm_num)
    · change wf_uN (lsize (lanetype_Jnn ty)) (.mk_uN (proj_uN_0 (Option.get! (proj_lane__0
        ((lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN before.toNat))[index]!)))))
      rw [selected]
      exact unsigned_wf_of_lt _ word.toNat word.isLt
  · rename_i outside
    apply StepH.step
    apply Step.vstore_lane_oob
    · simp [proj_num__0]
    · simpa only [lane_byte_count,proj_num__0,proj_uN_0,Option.get!_some] using
        (Nat.lt_of_not_ge outside)
    · exact input
    · exact wf_config_trap storeWf frameWf
    · exact Segment.index_wf 0 (by norm_num)
end Itasca.Runtime.Spec.Simd

end

/-! ## MemorySplat -/

section

/-!
Returned and trapping source behavior of vector splat loads.

Main declarations: `splat_load_value` and `splat_load_trap`. A direct consumer is `Interp.Simd.Memory.SplatSource`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt SpecExt.Builtins
theorem splat_load_value (ty : Jnn) (s : store) (f : frame) (argument : memarg) (address : Nat)
    (result : BitVec 128) (word : BitVec (lsize (lanetype_Jnn ty)))
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.VLOAD .V128 (some (.SPLAT (.mk_sz (lsize (lanetype_Jnn ty))))) argument))
    (bytesEq : ibytes_ (lsize (lanetype_Jnn ty)) (.mk_uN word.toNat) =
      ((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.drop (address+proj_uN_0 argument.OFFSET)).take (lsize (lanetype_Jnn ty)/8))
    (packed : uN.mk_uN result.toNat = inv_lanes_ (shapeOf (lanetype_Jnn ty))
      (List.replicate (128/lsize (lanetype_Jnn ty)) (.mk_lane__0 ty (.mk_uN word.toNat)))) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,
      .VLOAD .V128 (some (.SPLAT (.mk_sz (lsize (lanetype_Jnn ty))))) argument]⟩ []
      ⟨⟨s,f⟩,[.VCONST .V128 (.mk_uN result.toNat)]⟩ := by
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [Segment.i32 address,
        .VLOAD .V128 (some (.SPLAT (.mk_sz (lsize (lanetype_Jnn ty))))) argument] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact operationWf)
  have output := wf_config_make storeWf frameWf (show Forall wf_admininstr [.VCONST .V128 (.mk_uN result.toNat)] from by
    simpa [Forall] using const_wf result)
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  apply Step_read.vload_splat_val _ _ _ _ _ (.mk_uN word.toNat) ty (128/lsize (lanetype_Jnn ty))
  · simp [proj_num__0]
  · simpa only [lane_byte_count,proj_num__0,proj_uN_0,Option.get!_some] using bytesEq
  · cases ty <;> rfl
  · exact lane_dimension ty
  · simpa only [shapeOf,List.modify_eq_set,proj_uN_0] using packed
  · exact input
  · exact const_wf result
  · exact Segment.index_wf 0 (by norm_num)
  · exact shape_of_wf _
  · cases ty <;> exact lane_of_bits_wf _ word.toNat word.isLt

theorem splat_load_trap (ty : Jnn) (s : store) (f : frame) (argument : memarg) (address : Nat)
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.VLOAD .V128 (some (.SPLAT (.mk_sz (lsize (lanetype_Jnn ty))))) argument))
    (outside : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length < address+proj_uN_0 argument.OFFSET+lsize (lanetype_Jnn ty)/8) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,
      .VLOAD .V128 (some (.SPLAT (.mk_sz (lsize (lanetype_Jnn ty))))) argument]⟩ [] ⟨⟨s,f⟩,[.TRAP]⟩ := by
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [Segment.i32 address,
        .VLOAD .V128 (some (.SPLAT (.mk_sz (lsize (lanetype_Jnn ty))))) argument] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact operationWf)
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_trap storeWf frameWf)
  apply Step_read.vload_splat_oob
  · simp [proj_num__0]
  · simpa only [lane_byte_count,proj_num__0,proj_uN_0,Option.get!_some] using outside
  · exact input
  · exact .admininstr_case_73
  · exact Segment.index_wf 0 (by norm_num)
end Itasca.Runtime.Spec.Simd

end

/-! ## MemoryStore -/

section

/-!
Source reduction for bounded full-vector stores.

Main declarations: `full_store_step`. A direct consumer is `Interp.Simd.Memory.StoreSource`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt
theorem full_store_step (s : store) (f : frame) (argument : memarg) (address : Nat) (value : BitVec 128)
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.VSTORE .V128 argument))
    (mapped : 0 < f.MODULE.MEMS.length) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,.VCONST .V128 (.mk_uN value.toNat),.VSTORE .V128 argument]⟩ []
      (if address + proj_uN_0 argument.OFFSET + 16 ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length then
        ⟨⟨memoryPayloadWrite s f (address + proj_uN_0 argument.OFFSET) (vbytes_ .V128 (.mk_uN value.toNat)),f⟩,[]⟩
      else ⟨⟨s,f⟩,[.TRAP]⟩) := by
  have byteCount : rat_to_nat ((Option.get! (size valtype.V128) : Rat) / 8) = 16 := by
    norm_num [size,rat_to_nat]
    rfl
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr [Segment.i32 address,.VCONST .V128 (.mk_uN value.toNat),.VSTORE .V128 argument] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact const_wf value
    · exact operationWf)
  split
  · rename_i inside
    have updatedWf := memory_payload_write_wf s f (address+proj_uN_0 argument.OFFSET) (vbytes_ .V128 (.mk_uN value.toNat))
      storeWf (by exact integer_bytes_wf 16 value.toNat)
    apply StepH.step
    apply Step.vstore_val _ _ _ _ (vbytes_ .V128 (.mk_uN value.toNat))
    · simp [proj_num__0]
    · decide
    · exact .fun_with_mem_case_0 s f (.mk_uN 0) _ _ _ mapped
        (by simpa only [byteCount,proj_num__0,proj_uN_0,Option.get!_some] using inside)
        (.state_case_0 _ _ updatedWf frameWf) (.state_case_0 _ _ storeWf frameWf)
    · rfl
    · exact input
    · exact wf_config_make updatedWf frameWf (forall_nil _)
  · rename_i outside
    apply StepH.step
    apply Step.vstore_oob
    · simp [proj_num__0]
    · decide
    · simpa only [byteCount,proj_num__0,proj_uN_0,Option.get!_some] using Nat.lt_of_not_ge outside
    · exact input
    · exact wf_config_trap storeWf frameWf
    · exact Segment.index_wf 0 (by norm_num)
end Itasca.Runtime.Spec.Simd

end

/-! ## MemoryZero -/

section

/-!
The source result relation for zero-extending vector loads.

Main declarations: `zeroLoadResult`. A direct consumer is `Interp.Simd.Memory.ZeroSource`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt SpecExt.Builtins

def zeroLoadResult (width : Nat) (bytes : List byte) (start : Nat) : List admininstr :=
  if start + width/8 ≤ bytes.length then
    [.VCONST .V128 (.mk_uN (integerOfBytes ((bytes.drop start).take (width/8))))]
  else [.TRAP]

theorem zero_load_step (width : Nat) (supported : width = 32 ∨ width = 64)
    (s : store) (f : frame) (argument : memarg) (address : Nat)
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.VLOAD .V128 (some (.ZERO (.mk_sz width))) argument))
    (bytesWf : Forall wf_byte (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,.VLOAD .V128 (some (.ZERO (.mk_sz width))) argument]⟩ []
      ⟨⟨s,f⟩,zeroLoadResult width (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES
        (address + proj_uN_0 argument.OFFSET)⟩ := by
  have byteCount : rat_to_nat ((width : Rat) / 8) = width/8 := by
    rcases supported with rfl | rfl <;> norm_num [rat_to_nat] <;> rfl
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [Segment.i32 address,.VLOAD .V128 (some (.ZERO (.mk_sz width))) argument] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact operationWf)
  unfold zeroLoadResult
  split
  · rename_i fits
    let bytes := (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES
    let start := address + proj_uN_0 argument.OFFSET
    have payloadWf : Forall wf_byte ((bytes.drop start).take (width/8)) := by
      intro byte member
      exact bytesWf byte (List.mem_of_mem_drop (List.mem_of_mem_take member))
    have payloadLength : ((bytes.drop start).take (width/8)).length = width/8 := by
      simp only [List.length_take,List.length_drop]
      dsimp only [bytes,start]
      omega
    have bounded := integer_of_bytes_bound _ payloadWf
    rw [payloadLength] at bounded
    have narrow : wf_uN width (.mk_uN (integerOfBytes ((bytes.drop start).take (width/8)))) := by
      apply unsigned_wf_of_lt
      rcases supported with rfl | rfl <;> norm_num at bounded ⊢ <;> exact bounded
    have valueWf : wf_admininstr (.VCONST .V128 (.mk_uN (integerOfBytes ((bytes.drop start).take (width/8))))) := by
      apply wf_admininstr.admininstr_case_20 _ _ (by decide)
      apply unsigned_wf_of_lt
      rcases supported with rfl | rfl <;> norm_num [size,valtype_vectype] at bounded ⊢ <;> omega
    have output := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [.VCONST .V128 (.mk_uN (integerOfBytes ((bytes.drop start).take (width/8))))] from by
      simpa [Forall] using valueWf)
    apply StepH.step
    apply Step.read _ _ _ ?_ input output
    apply Step_read.vload_zero_val _ _ _ _ _ (.mk_uN (integerOfBytes ((bytes.drop start).take (width/8))))
    · simp [proj_num__0]
    · have roundtrip := integer_bytes_of_bytes _ payloadWf
      rw [payloadLength] at roundtrip
      simpa only [ibytes_,proj_uN_0,byteCount,proj_num__0,Option.get!_some,bytes,start,payloadLength]
        using roundtrip
    · rfl
    · exact narrow
    · exact input
    · exact valueWf
    · exact Segment.index_wf 0 (by norm_num)
  · rename_i outside
    apply StepH.step
    apply Step.read _ _ _ ?_ input (wf_config_trap storeWf frameWf)
    apply Step_read.vload_zero_oob
    · simp [proj_num__0]
    · simpa only [byteCount,proj_num__0,proj_uN_0,Option.get!_some] using Nat.lt_of_not_ge outside
    · exact input
    · exact .admininstr_case_73
    · exact Segment.index_wf 0 (by norm_num)
end Itasca.Runtime.Spec.Simd

end

/-! ## FloatUnary -/

section

/-!
Source-rule algebra for unary floating-point lanes. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Float Unary -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def floatUnaryChoices (width : Nat) (op : vunop_Fnn_N) (a : fN) : List fN :=
  match op with
  | .ABS => fabs_ width a
  | .NEG => fneg_ width a
  | .SQRT => fsqrt_ width a
  | .CEIL => fceil_ width a
  | .FLOOR => ffloor_ width a
  | .TRUNC => ftrunc_ width a
  | .NEAREST => fnearest_ width a

def floatUnarySource (ty : Fnn) (op : vunop_Fnn_N) : vunop_ :=
  .mk_vunop__1 ty (128/lsize (lanetype_Fnn ty)) op

theorem float_unary_source_wf (ty : Fnn) (op : vunop_Fnn_N) :
    wf_vunop_ (shapeOf (lanetype_Fnn ty)) (floatUnarySource ty op) := by
  cases ty <;> cases op <;> constructor <;> constructor

theorem float_unary_choices_wf (width : Nat) (supported : width = 32 ∨ width = 64)
    (op : vunop_Fnn_N) (a : fN) (inputWf : wf_fN width a) :
    Forall (wf_fN width) (floatUnaryChoices width op a) := by
  cases op with
  | ABS =>
    intro result member
    simp only [floatUnaryChoices,fabs_,List.mem_singleton] at member
    subst result
    exact withSign_wf (magnitude_wf inputWf) false
  | NEG =>
    intro result member
    simp only [floatUnaryChoices,fneg_,List.mem_singleton] at member
    subst result
    exact withSign_wf (magnitude_wf inputWf) _
  | SQRT => exact sqrt_wf width supported a inputWf
  | CEIL => exact integral_wf width supported _ a inputWf
  | FLOOR => exact integral_wf width supported _ a inputWf
  | TRUNC => exact integral_wf width supported _ a inputWf
  | NEAREST => exact integral_wf width supported _ a inputWf

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Float Unary Source -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def floatUnaryLaneChoices (ty : Fnn) (op : vunop_Fnn_N) (lane : lane_) : List lane_ :=
  Map (lane_.mk_lane__1 ty) (floatUnaryChoices (lsize (lanetype_Fnn ty)) op (Option.get! (proj_lane__1 lane)))

def floatUnaryResults (ty : Fnn) (op : vunop_Fnn_N) (bits : BitVec 128) : List uN :=
  Map (inv_lanes_ (shapeOf (lanetype_Fnn ty)))
    (setproduct_ lane_ (Map (floatUnaryLaneChoices ty op)
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN bits.toNat))))

theorem float_unary_lanes_wf (ty : Fnn) (op : vunop_Fnn_N) (bits : BitVec 128) :
    Forall (fun lane => Forall (fun value => wf_lane_ (lanetype_Fnn ty) (.mk_lane__1 ty value))
      (floatUnaryChoices (lsize (lanetype_Fnn ty)) op (Option.get! (proj_lane__1 lane))))
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN bits.toNat)) := by
  rw [lanes_map_words]
  intro lane member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  have inputWf : wf_fN (lsize (lanetype_Fnn ty))
      (Option.get! (proj_lane__1 (laneOfBits (lanetype_Fnn ty) (laneWord (lanetype_Fnn ty) bits j).toNat))) := by
    cases ty <;> exact floatOfBits_wf _ (by decide) _
  intro value allowed
  have wf := float_unary_choices_wf (lsize (lanetype_Fnn ty)) (by cases ty <;> decide) op _ inputWf value allowed
  cases ty <;> exact .lane__case_1 _ _ _ wf rfl

theorem float_unary_relation (ty : Fnn) (op : vunop_Fnn_N) (bits : BitVec 128) :
    fun_vunop_ (shapeOf (lanetype_Fnn ty)) (floatUnarySource ty op)
      (.mk_uN bits.toNat) (some (floatUnaryResults ty op bits)) := by
  have shapeWf := shape_of_wf (lanetype_Fnn ty)
  have lanesWf := float_unary_lanes_wf ty op bits
  cases ty <;> cases op
  · apply fun_vunop_.fun_vunop__case_12
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_14
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_16
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_18
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_20
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_22
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_24
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_13
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_15
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_17
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_19
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_21
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_23
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_25
    all_goals first | rfl | exact shapeWf | exact lanesWf

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Float Unary Choices -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem lanes_roundtrip (ty : lanetype) (bits : BitVec 128) :
    inv_lanes_ (shapeOf ty) (lanes_ (shapeOf ty) (.mk_uN bits.toNat)) = .mk_uN bits.toNat := by
  change uN.mk_uN (packLanes ty (unpackLanes ty (128/lsize ty) bits.toNat)) = _
  rw [pack_unpackLanes,shape_of_covers,Nat.mod_eq_of_lt bits.isLt]

theorem float_unary_result_member (ty : Fnn) (op : vunop_Fnn_N) (x result : BitVec 128)
    (allowed : ∀ j, j < 128/lsize (lanetype_Fnn ty) →
      floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) result j).toNat ∈
        floatUnaryChoices (lsize (lanetype_Fnn ty)) op
          (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat)) :
    uN.mk_uN result.toNat ∈ floatUnaryResults ty op x := by
  apply List.mem_map.mpr
  refine ⟨lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN result.toNat),?_,lanes_roundtrip _ result⟩
  rw [lanes_map_words,lanes_map_words]
  change List.map _ _ ∈ setproduct_ _ (List.map _ (List.map _ _))
  rw [List.map_map]
  apply mem_setproduct_map
  intro j member
  have chosen := allowed j (List.mem_range.mp member)
  cases ty <;> exact List.mem_map.mpr ⟨_,chosen,rfl⟩

theorem float_unary_step (ty : Fnn) (op : vunop_Fnn_N) (x result : BitVec 128)
    (allowed : ∀ j, j < 128/lsize (lanetype_Fnn ty) →
      floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) result j).toNat ∈
        floatUnaryChoices (lsize (lanetype_Fnn ty)) op
          (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat)) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),
      .VUNOP (shapeOf (lanetype_Fnn ty)) (floatUnarySource ty op)] [.VCONST .V128 (.mk_uN result.toNat)] := by
  have chosen := float_unary_result_member ty op x result allowed
  apply Step_pure.vunop _ _ _ _ (some (floatUnaryResults ty op x)) (float_unary_relation ty op x)
  · exact List.length_pos_of_mem chosen
  · simp
  · simpa only [Option.get!_some,List.contains_iff_mem] using chosen
  · exact const_wf x
  · exact .admininstr_case_25 _ _ (shape_of_wf _) (float_unary_source_wf ty op)
  · exact const_wf result

end Itasca.Runtime.Spec.Simd

end

end

/-! ## FloatResize -/

section

/-!
Source-rule algebra for floating-point lane promotion and demotion. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Float Resize -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

inductive FloatResize where | demote | promote

def FloatResize.input : FloatResize → Fnn | .demote => .F64 | .promote => .F32

def FloatResize.output : FloatResize → Fnn | .demote => .F32 | .promote => .F64

def floatResizeChoices : FloatResize → fN → List fN
  | .demote,a => demote__ 64 32 a
  | .promote,a => promote__ 32 64 a

def floatResizeSource (kind : FloatResize) : vcvtop__ :=
  match kind with
  | .demote => .mk_vcvtop___3 .F64 2 .F32 4 (.DEMOTE .ZERO)
  | .promote => .mk_vcvtop___3 .F32 4 .F64 2 .PROMOTELOW

theorem float_resize_source_wf (kind : FloatResize) :
    wf_vcvtop__ (shapeOf (lanetype_Fnn kind.input)) (shapeOf (lanetype_Fnn kind.output)) (floatResizeSource kind) := by
  cases kind <;> apply wf_vcvtop__.vcvtop___case_3
  · exact .vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_0 _ _ _ _ _ (by decide)
  · rfl
  · rfl
  · exact .vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_1 _ _ _ _ (by decide)
  · rfl
  · rfl

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Float Resize Source -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def floatResizeLaneChoices (kind : FloatResize) (a : fN) : List lane_ :=
  Map (lane_.mk_lane__1 kind.output) (floatResizeChoices kind a)

def floatResizeInputs (kind : FloatResize) (x : BitVec 128) : List lane_ :=
  (List.range 2).map (fun j => laneOfBits (lanetype_Fnn kind.input) (laneWord (lanetype_Fnn kind.input) x j).toNat)

def floatResizeChoicesList (kind : FloatResize) (x : BitVec 128) : List (Option (List lane_)) :=
  (List.range 2).map (fun j => some (floatResizeLaneChoices kind
    (floatOfBits (lsize (lanetype_Fnn kind.input)) (laneWord (lanetype_Fnn kind.input) x j).toNat)))

def floatResizePadding (kind : FloatResize) : List (List lane_) :=
  match kind with
  | .demote => List.replicate 2 [.mk_lane__1 .F32 (floatOfBits 32 0)]
  | .promote => []

def floatResizeProducts (kind : FloatResize) (x : BitVec 128) : List (List lane_) :=
  setproduct_ lane_ (Map Option.get! (floatResizeChoicesList kind x) ++ floatResizePadding kind)

theorem float_resize_lane_relation (kind : FloatResize) (value : fN) :
    fun_lcvtop__ (shapeOf (lanetype_Fnn kind.input)) (shapeOf (lanetype_Fnn kind.output)) (floatResizeSource kind)
      (.mk_lane__1 kind.input value) (some (floatResizeLaneChoices kind value)) := by
  have wf : Forall (fun result => wf_lane_ (lanetype_Fnn kind.output) (.mk_lane__1 kind.output result)) (floatResizeChoices kind value) := by
    intro result member
    cases kind
    · exact .lane__case_1 _ _ _ (Itasca.Runtime.Spec.float_demote_wf 64 32 (by decide) value result member) rfl
    · exact .lane__case_1 _ _ _ (Itasca.Runtime.Spec.float_demote_wf 32 64 (by decide) value result member) rfl
  cases kind
  · exact .fun_lcvtop___case_29 _ _ _ _ _ _ rfl wf rfl rfl
  · exact .fun_lcvtop___case_34 _ _ _ _ _ _ rfl wf rfl rfl

theorem float_resize_lists_relation (kind : FloatResize) (x : BitVec 128) :
    Forall₂ (fun choices input => fun_lcvtop__ (shapeOf (lanetype_Fnn kind.input))
      (shapeOf (lanetype_Fnn kind.output)) (floatResizeSource kind) input choices)
      (floatResizeChoicesList kind x) (floatResizeInputs kind x) := by
  apply forall2_map
  intro j member
  cases kind <;> exact float_resize_lane_relation _ _

theorem float_resize_product_member (kind : FloatResize) (x result : BitVec 128)
    (allowed : ∀ j, j < 2 →
      floatOfBits (lsize (lanetype_Fnn kind.output)) (laneWord (lanetype_Fnn kind.output) result j).toNat ∈
        floatResizeChoices kind (floatOfBits (lsize (lanetype_Fnn kind.input)) (laneWord (lanetype_Fnn kind.input) x j).toNat))
    (zeroed : ∀ j, 2 ≤ j → j < 128/lsize (lanetype_Fnn kind.output) → laneWord (lanetype_Fnn kind.output) result j = 0) :
    lanes_ (shapeOf (lanetype_Fnn kind.output)) (.mk_uN result.toNat) ∈ floatResizeProducts kind x := by
  rw [lanes_map_words]
  cases kind
  · change (List.range 4).map _ ∈ setproduct_ lane_ ((List.range 4).map (fun j =>
      if j < 2 then floatResizeLaneChoices .demote (floatOfBits 64 (laneWord .F64 x j).toNat)
      else [.mk_lane__1 .F32 (floatOfBits 32 0)]))
    apply mem_setproduct_map
    intro j member
    by_cases valid : j < 2
    · rw [if_pos valid]
      exact List.mem_map.mpr ⟨_,allowed j valid,rfl⟩
    · rw [if_neg valid]
      have zero := zeroed j (by omega) (List.mem_range.mp member)
      change laneWord .F32 result j = 0 at zero
      change lane_.mk_lane__1 .F32 (floatOfBits 32 (laneWord .F32 result j).toNat) ∈ _
      rw [zero]
      exact List.mem_cons_self
  · change (List.range 2).map _ ∈ setproduct_ lane_ ((List.range 2).map (fun j =>
      floatResizeLaneChoices .promote (floatOfBits 32 (laneWord .F32 x j).toNat)))
    apply mem_setproduct_map
    intro j member
    exact List.mem_map.mpr ⟨_,allowed j (List.mem_range.mp member),rfl⟩

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Float Resize Step -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

theorem float_resize_vector_relation (kind : FloatResize) (x result : BitVec 128)
    (selected : lanes_ (shapeOf (lanetype_Fnn kind.output)) (.mk_uN result.toNat) ∈ floatResizeProducts kind x) :
    fun_vcvtop__ (shapeOf (lanetype_Fnn kind.input)) (shapeOf (lanetype_Fnn kind.output)) (floatResizeSource kind)
      (.mk_uN x.toNat) (some (.mk_uN result.toNat)) := by
  let choices := floatResizeChoicesList kind x
  let inputs := floatResizeInputs kind x
  let products := floatResizeProducts kind x
  have nonempty : Forall (fun c => c ≠ none) choices := by
    intro c member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    simp
  have lengths : choices.length = inputs.length := by
    simp [choices,inputs,floatResizeChoicesList,floatResizeInputs]
  have member : (.mk_uN result.toNat) ∈ Map (inv_lanes_ (shapeOf (lanetype_Fnn kind.output))) products :=
    List.mem_map.mpr ⟨_,selected,lanes_roundtrip _ result⟩
  have wf := unsigned_wf_of_lt 128 result.toNat result.isLt
  cases kind
  · apply fun_vcvtop__.fun_vcvtop___case_2 .F64 2 .F32 4 (floatResizeSource .demote)
      (.mk_uN x.toNat) (.mk_uN result.toNat) inputs products (.mk_num__1 .F32 (floatOfBits 32 0))
      (some (.mk_lane__1 .F32 (floatOfBits 32 0))) choices (some (some .ZERO))
    · apply fun_zero.fun_zero_case_2
      · decide
      · exact .fun_fzero_case_0 _ (floatOfBits_wf 32 (by decide) 0)
      · exact Itasca.Runtime.Spec.float_num_wf .F32 _ (floatOfBits_wf 32 (by decide) _)
    · constructor; exact .lane__case_1 _ _ _ (floatOfBits_wf 32 (by decide) _) rfl
    · exact lengths
    · exact float_resize_lists_relation .demote x
    · exact .fun_zeroop_case_33 _ _ _ _ _ rfl rfl
    · simp
    · rfl
    · change inputs = lanes_ (shapeOf .F64) (.mk_uN x.toNat)
      rw [lanes_map_words]; rfl
    · exact nonempty
    · simp
    · rfl
    · exact List.length_pos_of_mem member
    · simpa only [List.contains_iff_mem,FloatResize.output,lanetype_Fnn,shapeOf,lsize,size,valtype_numtype,Option.get!_some] using member
    · exact wf
    · exact shape_of_wf _
    · exact shape_of_wf _
  · apply fun_vcvtop__.fun_vcvtop___case_1 .F32 4 .F64 2 (floatResizeSource .promote)
      (.mk_uN x.toNat) (.mk_uN result.toNat) .LOW inputs products choices (some (some .LOW))
    · exact lengths
    · exact float_resize_lists_relation .promote x
    · exact .fun_halfop_case_38 _ _ _ _ rfl rfl
    · simp
    · rfl
    · change inputs = List.take 2 (List.drop (fun_half .LOW 0 2) (lanes_ (shapeOf .F32) (.mk_uN x.toNat)))
      rw [lanes_map_words]; rfl
    · exact nonempty
    · rfl
    · exact List.length_pos_of_mem member
    · simpa only [List.contains_iff_mem,FloatResize.output,lanetype_Fnn,shapeOf,lsize,size,valtype_numtype,Option.get!_some] using member
    · exact wf
    · exact shape_of_wf _
    · exact shape_of_wf _

theorem float_resize_step (kind : FloatResize) (x result : BitVec 128)
    (allowed : ∀ j, j < 2 →
      floatOfBits (lsize (lanetype_Fnn kind.output)) (laneWord (lanetype_Fnn kind.output) result j).toNat ∈
        floatResizeChoices kind (floatOfBits (lsize (lanetype_Fnn kind.input)) (laneWord (lanetype_Fnn kind.input) x j).toNat))
    (zeroed : ∀ j, 2 ≤ j → j < 128/lsize (lanetype_Fnn kind.output) → laneWord (lanetype_Fnn kind.output) result j = 0) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),
      .VCVTOP (shapeOf (lanetype_Fnn kind.output)) (shapeOf (lanetype_Fnn kind.input)) (floatResizeSource kind)]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  have selected := float_resize_product_member kind x result allowed zeroed
  apply Step_pure.vcvtop _ _ _ _ _ (some (.mk_uN result.toNat))
  · exact float_resize_vector_relation kind x result selected
  · simp
  · rfl
  · exact const_wf x
  · apply wf_admininstr.admininstr_case_39
    · exact shape_of_wf _
    · exact shape_of_wf _
    · exact float_resize_source_wf kind
  · exact const_wf result

end Itasca.Runtime.Spec.Simd

end

end
