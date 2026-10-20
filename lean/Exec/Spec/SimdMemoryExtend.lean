import Exec.Spec.SimdMemoryChunks
import Exec.Spec.SimdMemoryLane
import Exec.Spec.SimdWidenLists
import Exec.Spec.SimdCompareFloatLists
namespace Exec.Spec.Simd
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
  · cases ty <;> exact shapeOf_wf _
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
end Exec.Spec.Simd
namespace Exec.Spec.Simd
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
end Exec.Spec.Simd
