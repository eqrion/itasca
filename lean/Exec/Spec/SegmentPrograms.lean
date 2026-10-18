import Exec.Spec.SegmentInitCases
import Mathlib.Data.List.Forall2
namespace Exec.Spec.Segment

/-- The initialization program prescribed by the generated element rule. -/
def elementProgram : elem → idx → List instr
  | .ELEM _ expressions mode, index => match mode with
    | .PASSIVE => []
    | .DECLARE => [.ELEM_DROP index]
    | .ACTIVE table offset => offset ++
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN 0)),
         .CONST .I32 (.mk_num__0 .I32 (.mk_uN expressions.length)),
         .TABLE_INIT table index, .ELEM_DROP index]

/-- The initialization program for a single-memory data segment. -/
def dataProgram : data → idx → List instr
  | .DATA bytes mode, index => match mode with
    | .PASSIVE => []
    | .ACTIVE _ offset => offset ++
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN 0)),
         .CONST .I32 (.mk_num__0 .I32 (.mk_uN bytes.length)),
         .MEMORY_INIT index, .DATA_DROP index]

def elementSize : elem → Nat
  | .ELEM _ expressions _ => expressions.length

def dataSize : data → Nat
  | .DATA bytes _ => bytes.length

def singleMemoryData : data → Prop
  | .DATA _ (.ACTIVE memory _) => memory = .mk_uN 0
  | .DATA _ .PASSIVE => True

private theorem const_wf (bits : Nat) (bound : bits < 2^32) :
    wf_instr (.CONST .I32 (.mk_num__0 .I32 (.mk_uN bits))) :=
  .instr_case_13 _ _ (.num__case_0 .I32 .I32 _ (by decide) (index_wf bits bound) rfl)

theorem element_program (segment : elem) (index : idx)
    (valid : wf_elem segment) (bounded : elementSize segment < 2^32)
    (indexWf : wf_uN 32 index) :
    fun_runelem segment index (elementProgram segment index) ∧
      Forall wf_instr (elementProgram segment index) := by
  cases valid with
  | elem_case_0 ty expressions mode exprWf modeWf =>
    cases modeWf with
    | elemmode_case_1 => exact ⟨.fun_runelem_case_0 _ _ _, by simp [elementProgram,Forall]⟩
    | elemmode_case_2 =>
      have drop := wf_instr.instr_case_55 index indexWf
      exact ⟨.fun_runelem_case_1 _ _ _ drop, by simpa [elementProgram,Forall] using drop⟩
    | elemmode_case_0 table offset tableWf offsetWf =>
      have zero := const_wf 0 (by decide)
      have count := const_wf expressions.length bounded
      have init := wf_instr.instr_case_54 table index tableWf indexWf
      have drop := wf_instr.instr_case_55 index indexWf
      refine ⟨.fun_runelem_case_2 _ _ _ _ _ _ rfl zero count init drop, ?_⟩
      apply forall_append offsetWf
      simpa [Forall] using And.intro zero (And.intro count (And.intro init drop))

theorem data_program (segment : data) (index : idx)
    (valid : wf_data segment) (bounded : dataSize segment < 2^32)
    (single : singleMemoryData segment) (indexWf : wf_uN 32 index) :
    fun_rundata segment index (some (dataProgram segment index)) ∧
      Forall wf_instr (dataProgram segment index) := by
  cases valid with
  | data_case_0 bytes mode bytesWf modeWf =>
    cases modeWf with
    | datamode_case_1 => exact ⟨.fun_rundata_case_0 _ _, by simp [dataProgram,Forall]⟩
    | datamode_case_0 memory offset memoryWf offsetWf =>
      change memory = .mk_uN 0 at single
      subst memory
      have zero := const_wf 0 (by decide)
      have count := const_wf bytes.length bounded
      have init := wf_instr.instr_case_66 index indexWf
      have drop := wf_instr.instr_case_67 index indexWf
      refine ⟨.fun_rundata_case_1 _ _ _ _ rfl zero count init drop, ?_⟩
      apply forall_append offsetWf
      simpa [Forall] using And.intro zero (And.intro count (And.intro init drop))

def elementPrograms (segments : List elem) : List (List instr) :=
  (List.range segments.length).map (fun index => elementProgram segments[index]! (.mk_uN index))

def dataPrograms (segments : List data) : List (List instr) :=
  (List.range segments.length).map (fun index => dataProgram segments[index]! (.mk_uN index))

theorem element_programs (segments : List elem) (countBound : segments.length ≤ 2^32)
    (valid : ∀ segment ∈ segments, wf_elem segment ∧ elementSize segment < 2^32) :
    List.Forall₂ (fun index program => fun_runelem segments[index]! (.mk_uN index) program)
      (List.range segments.length) (elementPrograms segments) ∧
    Forall (fun program => Forall wf_instr program) (elementPrograms segments) := by
  have one : ∀ index ∈ List.range segments.length,
      fun_runelem segments[index]! (.mk_uN index) (elementProgram segments[index]! (.mk_uN index)) ∧
      Forall wf_instr (elementProgram segments[index]! (.mk_uN index)) := by
    intro index member
    have bound := List.mem_range.mp member
    have present : segments[index]! ∈ segments := by
      simpa only [getElem!_pos segments index bound] using List.getElem_mem bound
    exact element_program _ _ (valid _ present).1 (valid _ present).2 (index_wf _ (by omega))
  constructor
  · apply List.forall₂_map_right_iff.mpr
    exact List.forall₂_same.mpr (fun index member => (one index member).1)
  · intro program member
    obtain ⟨index, present, rfl⟩ := List.mem_map.mp member
    exact (one index present).2

theorem data_programs (segments : List data) (countBound : segments.length ≤ 2^32)
    (valid : ∀ segment ∈ segments, wf_data segment ∧ dataSize segment < 2^32 ∧ singleMemoryData segment) :
    List.Forall₂ (fun index program => fun_rundata segments[index]! (.mk_uN index) (some program))
      (List.range segments.length) (dataPrograms segments) ∧
    Forall (fun program => Forall wf_instr program) (dataPrograms segments) := by
  have one : ∀ index ∈ List.range segments.length,
      fun_rundata segments[index]! (.mk_uN index) (some (dataProgram segments[index]! (.mk_uN index))) ∧
      Forall wf_instr (dataProgram segments[index]! (.mk_uN index)) := by
    intro index member
    have bound := List.mem_range.mp member
    have present : segments[index]! ∈ segments := by
      simpa only [getElem!_pos segments index bound] using List.getElem_mem bound
    exact data_program _ _ (valid _ present).1 (valid _ present).2.1
      (valid _ present).2.2 (index_wf _ (by omega))
  constructor
  · apply List.forall₂_map_right_iff.mpr
    exact List.forall₂_same.mpr (fun index member => (one index member).1)
  · intro program member
    obtain ⟨index, present, rfl⟩ := List.mem_map.mp member
    exact (one index present).2

private theorem admin_programs_wf (programs : List (List instr))
    (valid : Forall (fun program => Forall wf_instr program) programs) :
    Forall wf_admininstr (programs.flatten.map admininstr_instr) := by
  intro instruction member
  obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨program, programPresent, present⟩ := List.mem_flatten.mp present
  exact wf_admininstr_instr (valid program programPresent source present)

/-- The generated instantiation result is syntactically well formed once its
allocated store, module frame, source segment programs, and start index are. -/
theorem initialization_config_wf (s : store) (inst : moduleinst)
    (elements datas : List (List instr)) (start : Option idx)
    (storeWf : wf_store s) (instanceWf : wf_moduleinst inst)
    (elementWf : Forall (fun program => Forall wf_instr program) elements)
    (dataWf : Forall (fun program => Forall wf_instr program) datas)
    (startWf : Forall (wf_uN 32) start.toList) :
    wf_config ⟨⟨s, ⟨[], inst⟩⟩,
      elements.flatten.map admininstr_instr ++
        (datas.flatten.map admininstr_instr ++ (start.map admininstr.CALL).toList)⟩ := by
  apply wf_config_make storeWf (.frame_case_ _ _ (by simp [Forall]) instanceWf)
  apply forall_append (admin_programs_wf elements elementWf)
  apply forall_append (admin_programs_wf datas dataWf)
  cases start with
  | none => simp [Forall]
  | some index =>
    have indexWf : wf_uN 32 index := by simpa [Forall] using startWf
    simpa [Forall] using wf_admininstr.admininstr_case_10 index indexWf
end Exec.Spec.Segment
