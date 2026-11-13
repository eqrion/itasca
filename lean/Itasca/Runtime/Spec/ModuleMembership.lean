import Itasca.Runtime.Spec.FloatPromote
import Itasca.Runtime.Spec.Integer
import Mathlib.Data.List.Forall2
import Mathlib.Tactic
import Itasca.Runtime.Spec.SegmentInitCases
import Itasca.Runtime.Spec.FloatTrunc
import Itasca.Runtime.Spec.Simd.Shape
import SpecExt.Builtins

/-!
Sections, each formerly its own module: IndirectCallSource, Invocation, Allocation, SegmentPrograms, Instantiation, AllocationModule, SplitCopy, PureWf, EventfulInfinite, HostCall, Depth, ModuleMembership.
-/

/-! ## IndirectCallSource -/

section

namespace Itasca.Runtime.Spec
open SpecExt

/-- The generated indirect-call rule resolves exactly a function reference
whose signature matches the module type selected by the instruction. -/
def IndirectTarget (s : store) (f : frame) (table type position address : Nat) : Prop :=
  (fun_table ⟨s,f⟩ (.mk_uN table)).REFS[position]? = some (.REF_FUNC_ADDR address) ∧
    ∃ function,s.FUNCS[address]?=some function ∧ fun_type ⟨s,f⟩ (.mk_uN type)=function.TYPE

theorem call_indirect_resolve (s : store) (f : frame) (table type position address : Nat)
    (hs : wf_store s) (hf : wf_frame f) (ht : table<2^32) (hy : type<2^32) (hp : position<2^32)
    (target : IndirectTarget s f table type position address) :
    StepH ⟨⟨s,f⟩,[Segment.i32 position,.CALL_INDIRECT (.mk_uN table) (.mk_uN type)]⟩ []
      ⟨⟨s,f⟩,[.CALL_ADDR address]⟩ := by
  have input : wf_config ⟨⟨s,f⟩,[Segment.i32 position,.CALL_INDIRECT (.mk_uN table) (.mk_uN type)]⟩ := by
    apply wf_config_make hs hf
    simp only [Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨Segment.i32_wf _ hp,.admininstr_case_11 _ _ (Segment.index_wf _ ht) (Segment.index_wf _ hy)⟩
  obtain ⟨inside,reference⟩ := List.getElem?_eq_some_iff.mp target.1
  obtain ⟨function,lookup,signature⟩ := target.2
  obtain ⟨issued,actual⟩ := List.getElem?_eq_some_iff.mp lookup
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_make hs hf (by simpa [Forall] using wf_admininstr.admininstr_case_70 address))
  apply Step_read.call_indirect_call ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN position)) (.mk_uN table) (.mk_uN type) address
  · exact inside
  · simp [proj_num__0]
  · simpa only [proj_num__0,proj_uN_0,Option.get!,getElem!_pos (fun_table ⟨s,f⟩ (.mk_uN table)).REFS position inside] using reference
  · exact issued
  · simpa only [fun_funcinst,getElem!_pos s.FUNCS address issued,actual] using signature
  · exact input
  · exact .admininstr_case_70 _

theorem call_indirect_trap (s : store) (f : frame) (table type position : Nat)
    (hs : wf_store s) (hf : wf_frame f) (ht : table<2^32) (hy : type<2^32) (hp : position<2^32)
    (missing : ¬∃address,IndirectTarget s f table type position address) :
    StepH ⟨⟨s,f⟩,[Segment.i32 position,.CALL_INDIRECT (.mk_uN table) (.mk_uN type)]⟩ [] ⟨⟨s,f⟩,[.TRAP]⟩ := by
  have input : wf_config ⟨⟨s,f⟩,[Segment.i32 position,.CALL_INDIRECT (.mk_uN table) (.mk_uN type)]⟩ := by
    apply wf_config_make hs hf
    simp only [Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨Segment.i32_wf _ hp,.admininstr_case_11 _ _ (Segment.index_wf _ ht) (Segment.index_wf _ hy)⟩
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_make hs hf (by simpa [Forall] using wf_admininstr.admininstr_case_73))
  apply Step_read.call_indirect_trap ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN position)) (.mk_uN table) (.mk_uN type) ?_ input .admininstr_case_73
  intro prior
  cases prior with
  | call_indirect_call_0 _ _ _ _ address inside numeric reference issued signature _ _ =>
    have inside' : position < (fun_table ⟨s,f⟩ (.mk_uN table)).REFS.length := inside
    have issued' : address < s.FUNCS.length := issued
    apply missing
    refine ⟨address,List.getElem?_eq_some_iff.mpr ⟨inside',?_⟩,s.FUNCS[address],List.getElem?_eq_getElem issued',?_⟩
    · simpa only [proj_num__0,proj_uN_0,Option.get!,getElem!_pos (fun_table ⟨s,f⟩ (.mk_uN table)).REFS position inside'] using reference
    · simpa only [fun_funcinst,getElem!_pos s.FUNCS address issued'] using signature
end Itasca.Runtime.Spec

end

/-! ## Invocation -/

section

namespace Itasca.Runtime.Spec
open SpecExt

/-- The generated invocation judgment fixes the ambient frame to the empty
module instance and emits the argument constants followed by CALL_ADDR. -/
def invocationFrame : frame := ⟨[], ⟨[], [], [], [], [], [], [], []⟩⟩

theorem invocation_config {s : store} {address : funcaddr} {args : List val} {initial : config}
    (invoked : fun_invoke s address args initial) :
    initial = ⟨⟨s, invocationFrame⟩, vals args ++ [.CALL_ADDR address]⟩ := by
  cases invoked
  simp_all [invocationFrame, vals, Map]

theorem invocation_frame_wf {s : store} {address : funcaddr} {args : List val} {initial : config}
    (invoked : fun_invoke s address args initial) : wf_frame invocationFrame := by
  cases invoked
  assumption
end Itasca.Runtime.Spec

end

/-! ## Allocation -/

section

namespace Itasca.Runtime.Spec
open SpecExt

def allocationFunctionIndex : func → Nat
  | .FUNC (.mk_uN index) _ _ => index

def allocationFunction (inst : moduleinst) (source : func) : funcinst :=
  ⟨inst.TYPES[allocationFunctionIndex source]!, inst, funccode_func source⟩

def allocationTable : tabletype → tableinst
  | .mk_tabletype (.mk_limits (.mk_uN minimum) maximum) ty =>
    ⟨.mk_tabletype (.mk_limits (.mk_uN minimum) maximum) ty, List.replicate minimum (.REF_NULL ty)⟩

def allocationMemory : memtype → meminst
  | .PAGE (.mk_limits (.mk_uN minimum) maximum) =>
    ⟨.PAGE (.mk_limits (.mk_uN minimum) maximum), List.replicate (minimum * (64 * Ki)) (.mk_byte 0)⟩

theorem allocation_function_wf (inst : moduleinst) (source : func)
    (instanceWf : wf_moduleinst inst) (sourceWf : wf_func source) : wf_funcinst (allocationFunction inst source) := by
  cases sourceWf with
  | func_case_0 index locals body indexWf bodyWf =>
    exact .funcinst_case_ _ _ _ instanceWf (.funccode_case_0 _ _ _ indexWf bodyWf)

theorem allocate_function (s : store) (inst : moduleinst) (source : func)
    (instanceWf : wf_moduleinst inst) (sourceWf : wf_func source)
    (bound : allocationFunctionIndex source < inst.TYPES.length) :
    fun_allocfunc s inst source ({s with FUNCS := s.FUNCS ++ [allocationFunction inst source]}, s.FUNCS.length) := by
  have allocatedWf := allocation_function_wf inst source instanceWf sourceWf
  cases source with
  | FUNC index locals body =>
    exact .fun_allocfunc_case_0 s inst _ _ index locals body bound rfl rfl allocatedWf allocatedWf sourceWf

theorem allocate_global (s : store) (value : globalinst) (wf : wf_globalinst value) :
    fun_allocglobal s value.TYPE value.VALUE ({s with GLOBALS := s.GLOBALS ++ [value]}, s.GLOBALS.length) := by
  exact .fun_allocglobal_case_0 s value.TYPE value.VALUE value (by cases value; rfl) wf (by simpa using wf)

theorem allocate_table (s : store) (ty : tabletype) (wf : wf_tabletype ty) :
    fun_alloctable s ty ({s with TABLES := s.TABLES ++ [allocationTable ty]}, s.TABLES.length) := by
  cases ty with | mk_tabletype limits refType =>
    cases limits with | mk_limits minimum maximum =>
      cases minimum with | mk_uN minimum =>
        exact .fun_alloctable_case_0 s _ maximum refType _ rfl (.tableinst_case_ _ _ wf) (.tableinst_case_ _ _ wf)

theorem allocate_memory (s : store) (ty : memtype) (wf : wf_memtype ty) :
    fun_allocmem s ty ({s with MEMS := s.MEMS ++ [allocationMemory ty]}, s.MEMS.length) := by
  cases ty with | PAGE limits =>
    cases limits with | mk_limits minimum maximum =>
      cases minimum with | mk_uN minimum =>
        have bytes : Forall wf_byte (List.replicate (minimum * (64 * Ki)) (.mk_byte 0)) := by
          intro value member
          have same : value = .mk_byte 0 := (List.mem_replicate.mp member).2
          rw [same]; constructor; norm_num
        exact .fun_allocmem_case_0 s _ maximum _ rfl (.meminst_case_ _ _ wf bytes) (.meminst_case_ _ _ wf bytes)

theorem allocate_element (s : store) (element : eleminst) :
    fun_allocelem s element.TYPE element.REFS ({s with ELEMS := s.ELEMS ++ [element]}, s.ELEMS.length) := by
  exact .fun_allocelem_case_0 s element.TYPE element.REFS element (by cases element; rfl)

theorem allocate_data (s : store) (data : datainst) (wf : wf_datainst data) :
    fun_allocdata s data.BYTES ({s with DATAS := s.DATAS ++ [data]}, s.DATAS.length) := by
  exact .fun_allocdata_case_0 s data.BYTES data (by cases data; rfl) wf (by simpa using wf)

/-- Allocating a list appends its instances and issues precisely the consecutive
addresses starting at the old vector length. -/
theorem allocate_functions (s : store) (inst : moduleinst) (sources : List func)
    (instanceWf : wf_moduleinst inst) (sourceWf : Forall wf_func sources)
    (bounds : ∀ source ∈ sources, allocationFunctionIndex source < inst.TYPES.length) :
    fun_allocfuncs s inst sources
      ({s with FUNCS := s.FUNCS ++ sources.map (allocationFunction inst)}, List.range' s.FUNCS.length sources.length) := by
  induction sources generalizing s with
  | nil => simpa using fun_allocfuncs.fun_allocfuncs_case_0 s inst
  | cons source sources ih =>
    have one := allocate_function s inst source instanceWf (sourceWf source (by simp)) (bounds source (by simp))
    have rest := ih {s with FUNCS := s.FUNCS ++ [allocationFunction inst source]}
      (fun f hf => sourceWf f (by simp [hf])) (fun f hf => bounds f (by simp [hf]))
    simpa only [List.map_cons, List.length_cons, List.range'_succ, List.length_append,
      List.length_singleton, List.length_nil, Nat.zero_add, List.append_assoc, List.singleton_append] using
      fun_allocfuncs.fun_allocfuncs_case_1 s inst source sources _ _ _ _ _ _ rest one rfl rfl

theorem allocate_globals (s : store) (values : List globalinst)
    (wf : Forall wf_globalinst values) :
    fun_allocglobals s (values.map globalinst.TYPE) (values.map globalinst.VALUE)
      ({s with GLOBALS := s.GLOBALS ++ values}, List.range' s.GLOBALS.length values.length) := by
  induction values generalizing s with
  | nil => simpa using fun_allocglobals.fun_allocglobals_case_0 s
  | cons value values ih =>
    have one := allocate_global s value (wf value (by simp))
    have rest := ih {s with GLOBALS := s.GLOBALS ++ [value]}
      (fun value member => wf value (by simp [member]))
    simpa only [List.map_cons, List.length_cons, List.range'_succ, List.length_append,
      List.length_singleton, List.length_nil, Nat.zero_add, List.append_assoc, List.singleton_append] using
      fun_allocglobals.fun_allocglobals_case_1 s value.TYPE (values.map globalinst.TYPE) value.VALUE (values.map globalinst.VALUE) _ _ _ _ _ _ rest one rfl rfl

theorem allocate_tables (s : store) (values : List tabletype)
    (wf : Forall wf_tabletype values) :
    fun_alloctables s (values)
      ({s with TABLES := s.TABLES ++ values.map allocationTable}, List.range' s.TABLES.length values.length) := by
  induction values generalizing s with
  | nil => simpa using fun_alloctables.fun_alloctables_case_0 s
  | cons value values ih =>
    have one := allocate_table s value (wf value (by simp))
    have rest := ih {s with TABLES := s.TABLES ++ [allocationTable value]}
      (fun value member => wf value (by simp [member]))
    simpa only [List.map_cons, List.length_cons, List.range'_succ, List.length_append,
      List.length_singleton, List.length_nil, Nat.zero_add, List.append_assoc, List.singleton_append] using
      fun_alloctables.fun_alloctables_case_1 s value values _ _ _ _ _ _ rest one rfl rfl

theorem allocate_memories (s : store) (values : List memtype)
    (wf : Forall wf_memtype values) :
    fun_allocmems s (values)
      ({s with MEMS := s.MEMS ++ values.map allocationMemory}, List.range' s.MEMS.length values.length) := by
  induction values generalizing s with
  | nil => simpa using fun_allocmems.fun_allocmems_case_0 s
  | cons value values ih =>
    have one := allocate_memory s value (wf value (by simp))
    have rest := ih {s with MEMS := s.MEMS ++ [allocationMemory value]}
      (fun value member => wf value (by simp [member]))
    simpa only [List.map_cons, List.length_cons, List.range'_succ, List.length_append,
      List.length_singleton, List.length_nil, Nat.zero_add, List.append_assoc, List.singleton_append] using
      fun_allocmems.fun_allocmems_case_1 s value values _ _ _ _ _ _ rest one rfl rfl

theorem allocate_elements (s : store) (values : List eleminst) :
    fun_allocelems s (values.map eleminst.TYPE) (values.map eleminst.REFS)
      ({s with ELEMS := s.ELEMS ++ values}, List.range' s.ELEMS.length values.length) := by
  induction values generalizing s with
  | nil => simpa using fun_allocelems.fun_allocelems_case_0 s
  | cons value values ih =>
    have one := allocate_element s value
    have rest := ih {s with ELEMS := s.ELEMS ++ [value]}
    simpa only [List.map_cons, List.length_cons, List.range'_succ, List.length_append,
      List.length_singleton, List.length_nil, Nat.zero_add, List.append_assoc, List.singleton_append] using
      fun_allocelems.fun_allocelems_case_1 s value.TYPE (values.map eleminst.TYPE) value.REFS (values.map eleminst.REFS) _ _ _ _ _ _ rest one rfl rfl

theorem allocate_datas (s : store) (values : List datainst)
    (wf : Forall wf_datainst values) :
    fun_allocdatas s (values.map datainst.BYTES)
      ({s with DATAS := s.DATAS ++ values}, List.range' s.DATAS.length values.length) := by
  induction values generalizing s with
  | nil => simpa using fun_allocdatas.fun_allocdatas_case_0 s
  | cons value values ih =>
    have one := allocate_data s value (wf value (by simp))
    have rest := ih {s with DATAS := s.DATAS ++ [value]}
      (fun value member => wf value (by simp [member]))
    simpa only [List.map_cons, List.length_cons, List.range'_succ, List.length_append,
      List.length_singleton, List.length_nil, Nat.zero_add, List.append_assoc, List.singleton_append] using
      fun_allocdatas.fun_allocdatas_case_1 s value.BYTES (values.map datainst.BYTES) _ _ _ _ _ _ rest one rfl rfl

end Itasca.Runtime.Spec

end

/-! ## SegmentPrograms -/

section

namespace Itasca.Runtime.Spec.Segment

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
end Itasca.Runtime.Spec.Segment

end

/-! ## Instantiation -/

section

namespace Itasca.Runtime.Spec
open SpecExt

private theorem concat_flatten {A : Type} (programs : List (List A)) : concat_ A programs = programs.flatten := by
  induction programs with
  | nil => rfl
  | cons head tail ih => simp only [concat_, List.flatten_cons, ih]

private theorem wf_concat (programs : List (List instr))
    (wf : Forall (fun program => Forall wf_instr program) programs) :
    Forall wf_instr (concat_ instr programs) := by
  rw [concat_flatten]
  intro instruction member
  obtain ⟨program, present, member⟩ := List.mem_flatten.mp member
  exact wf program present instruction member

private theorem get_some_programs (indices : List Nat) (programs : List (List instr))
    (lengths : indices.length = programs.length) :
    (indices.map (fun _ (program : Option (List instr)) => Option.get! program)).ap
      (programs.map some) = programs := by
  induction indices generalizing programs with
  | nil => cases programs <;> simp_all [List.ap]
  | cons index rest ih =>
    cases programs with
    | nil => simp at lengths
    | cons program programs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at lengths
      simpa only [List.map_cons, List.ap, List.zipWith_cons_cons, Option.get!_some] using
        congrArg (program :: ·) (ih programs lengths)

/-- A compact constructor for the generated instantiation judgment. Repeated
allocation and segment premises in the generated rule are discharged from one
source derivation each; partial data programs are all present. -/
theorem instantiate_source
    (s after : store) (source : module) (externals : List externaddr)
    (types : List functype) (imports : List «import») (functions : List func)
    (globals : List global) (tables : List table) (memories : List mem)
    (elements : List elem) (datas : List data) (startIndex : Option idx) (exports : List «export»)
    (globalExprs : List expr) (globalTypes : List globaltype)
    (elementModes : List elemmode) (elementExprs : List (List expr)) (elementTypes : List reftype)
    (values : List val) (references : List (List ref))
    (importedFunctions : List funcaddr) (importedGlobals : List globaladdr)
    (inst : moduleinst) (elementPrograms dataPrograms : List (List instr))
    (sourceEq : source = .MODULE (types.map type.TYPE) imports functions globals tables memories
      elements datas (startIndex.map start.START) exports)
    (globalsEq : globals = Map₂ (fun expression ty => global.GLOBAL ty expression) globalExprs globalTypes)
    (elementsEq : elements = Map₃ (fun mode expressions ty => elem.ELEM ty expressions mode)
      elementModes elementExprs elementTypes)
    (importFunctions : fun_funcs externals importedFunctions)
    (importGlobals : fun_globals externals importedGlobals)
    (initialModule : moduleinst)
    (initialEq : initialModule = ⟨types,
      importedFunctions ++ (List.range functions.length).map (fun index => s.FUNCS.length + index),
      importedGlobals, [], [], [], [], []⟩)
    (globalCounts : globalExprs.length = values.length)
    (globalEval : Forall₂ (fun expression value => Eval_expr ⟨s, ⟨[], initialModule⟩⟩ expression
      ⟨s, ⟨[], initialModule⟩⟩ [value]) globalExprs values)
    (elementCounts : elementExprs.length = references.length)
    (elementValueCounts : Forall₂ (fun expressions values => expressions.length = values.length) elementExprs references)
    (elementEval : Forall₂ (fun expressions values => Forall₂ (fun expression value =>
      Eval_expr ⟨s, ⟨[], initialModule⟩⟩ expression ⟨s, ⟨[], initialModule⟩⟩ [val_ref value])
      expressions values) elementExprs references)
    (allocated : fun_allocmodule s source externals values references (after, inst))
    (runElements : List.Forall₂ (fun index program => fun_runelem elements[index]! (.mk_uN index) program)
      (List.range elements.length) elementPrograms)
    (runDatas : List.Forall₂ (fun index program => fun_rundata datas[index]! (.mk_uN index) (some program))
      (List.range datas.length) dataPrograms)
    (valuesWf : Forall wf_val values) (afterWf : wf_store after) (instWf : wf_moduleinst inst)
    (elementsWf : Forall (fun program => Forall wf_instr program) elementPrograms)
    (datasWf : Forall (fun program => Forall wf_instr program) dataPrograms)
    (configWf : wf_config ⟨⟨after, ⟨[], inst⟩⟩,
      elementPrograms.flatten.map admininstr_instr ++
      (dataPrograms.flatten.map admininstr_instr ++ (startIndex.map admininstr.CALL).toList)⟩)
    (sourceWf : wf_module source)
    (globalTypeCounts : globalExprs.length = globalTypes.length)
    (globalWf : Forall₂ (fun expression ty => wf_global (.GLOBAL ty expression)) globalExprs globalTypes)
    (elementModeCounts : elementModes.length = elementExprs.length)
    (elementTypeCounts : elementModes.length = elementTypes.length)
    (elementWf : Forall₃ (fun mode expressions ty => wf_elem (.ELEM ty expressions mode))
      elementModes elementExprs elementTypes)
    (startWf : Forall (fun index => wf_start (.START index)) startIndex.toList)
    (initialWf : wf_moduleinst initialModule) (storeWf : wf_store s)
    (elementBound : elements.length ≤ 2^32) (dataBound : datas.length ≤ 2^32) :
    fun_instantiate s source externals ⟨⟨after, ⟨[], inst⟩⟩,
      elementPrograms.flatten.map admininstr_instr ++
      (dataPrograms.flatten.map admininstr_instr ++ (startIndex.map admininstr.CALL).toList)⟩ := by
  have eb : Forall (fun index => index < elements.length) (List.range elements.length) := by
    intro index member; exact List.mem_range.mp member
  have db : Forall (fun index => index < datas.length) (List.range datas.length) := by
    intro index member; exact List.mem_range.mp member
  have elementRun : Forall₂ (fun index program => fun_runelem elements[index]! (.mk_uN index) program)
      (List.range elements.length) elementPrograms := fun _ member => List.forall₂_zip runElements member
  have dataRun : Forall₂ (fun index program => fun_rundata datas[index]! (.mk_uN index) program)
      (List.range datas.length) (dataPrograms.map some) := by
    exact fun _ member => List.forall₂_zip (List.forall₂_map_right_iff.mpr runDatas) member
  have flattened := get_some_programs (List.range datas.length) dataPrograms runDatas.length_eq
  have defined : Forall₂ (fun (_ : Nat) (program : Option (List instr)) => program ≠ none)
      (List.range datas.length) (dataPrograms.map some) := by
    intro pair member
    have present := List.of_mem_zip member |>.2
    obtain ⟨program, _, equal⟩ := List.mem_map.mp present
    simp [← equal]
  have initialFrame : wf_frame ⟨[], initialModule⟩ := .frame_case_ _ _ (by simp [Forall]) initialWf
  have finalFrame : wf_frame ⟨[], inst⟩ := .frame_case_ _ _ (by simp [Forall]) instWf
  have elementAll : Forall wf_instr (concat_ instr elementPrograms) := by
    exact wf_concat elementPrograms elementsWf
  have dataAll : Forall wf_instr (concat_ instr dataPrograms) := by
    exact wf_concat dataPrograms datasWf
  refine fun_instantiate.fun_instantiate_case_0 s source externals ⟨[], inst⟩ startIndex types globalExprs
    globalTypes elementModes elementExprs elementTypes initialModule ⟨[], initialModule⟩ values references
    0 0 (types.map type.TYPE) imports functions globals tables memories elements datas (startIndex.map start.START)
    exports functions.length elements.length datas.length ⟨s, ⟨[], initialModule⟩⟩ after inst
    elementPrograms.flatten dataPrograms.flatten importedGlobals importedFunctions
    (dataPrograms.map some) (dataPrograms.map some) elementPrograms elementPrograms
    (after, inst) (after, inst) (dataPrograms.map some) elementPrograms (after, inst)
    importedGlobals importedFunctions
    importGlobals importFunctions db dataRun db dataRun eb elementRun eb elementRun allocated allocated
    db dataRun eb elementRun allocated importGlobals importFunctions sourceEq.symm rfl globalsEq elementsEq rfl
    rfl rfl rfl initialEq rfl rfl globalCounts globalEval elementCounts elementValueCounts elementEval rfl rfl
    ?_ defined ?_ valuesWf afterWf instWf elementAll ?_ ?_ ?_ ?_ ?_ globalTypeCounts globalWf
    elementModeCounts elementTypeCounts elementWf startWf ?_ initialFrame (.state_case_0 _ _ storeWf initialFrame)
    finalFrame ?_ ?_
  · exact (concat_flatten elementPrograms).symm
  · simpa only [flattened] using (concat_flatten dataPrograms).symm
  · intro pair member
    exact elementsWf pair.2 ((List.of_mem_zip member).2)
  · simpa only [flattened] using dataAll
  · intro pair member
    obtain ⟨program, present, equal⟩ := List.mem_map.mp ((List.of_mem_zip member).2)
    simpa only [← equal, Option.get!_some] using datasWf program present
  · simpa only [Map, OMap] using configWf
  · simpa only [← sourceEq] using sourceWf
  · simpa only [initialEq] using initialWf
  · intro index member
    constructor
    have bound := (List.mem_range.mp member).trans_le elementBound
    norm_num at *
    omega
  · intro index member
    constructor
    have bound := (List.mem_range.mp member).trans_le dataBound
    norm_num at *
    omega
end Itasca.Runtime.Spec

end

/-! ## AllocationModule -/

section

namespace Itasca.Runtime.Spec
open SpecExt

def allocationStore (s : store) (inst : moduleinst) (functions : List func)
    (globals : List globalinst) (tables : List tabletype) (memories : List memtype)
    (elements : List eleminst) (datas : List datainst) : store :=
  ⟨s.FUNCS ++ functions.map (allocationFunction inst), s.GLOBALS ++ globals,
    s.TABLES ++ tables.map allocationTable, s.MEMS ++ memories.map allocationMemory,
    s.ELEMS ++ elements, s.DATAS ++ datas⟩

private theorem store_parts {s : store} (wf : wf_store s) :
    Forall wf_funcinst s.FUNCS ∧ Forall wf_globalinst s.GLOBALS ∧ Forall wf_tableinst s.TABLES ∧
      Forall wf_meminst s.MEMS ∧ Forall wf_datainst s.DATAS := by
  cases wf; exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption⟩

/-- Concrete list allocation proves the generated whole-module allocator.
The only retained allocation-side evidence is syntax, index bounds, the exact
published module layout, and the independently checked export resolutions. -/
theorem allocate_module (s : store) (source : module) (externals : List externaddr)
    (inst : moduleinst) (types : List functype) (imports : List «import») (functions : List func)
    (globals : List globalinst) (tables : List tabletype) (memories : List memtype)
    (elements : List eleminst) (datas : List datainst)
    (globalExpressions : List expr) (elementExpressions : List (List expr))
    (elementModes : List elemmode) (dataModes : List datamode) (start : Option start)
    (exports : List «export») (exportInstances : List exportinst)
    (importedFunctions importedGlobals importedTables importedMemories : List Nat)
    (sourceEq : source = .MODULE (types.map type.TYPE) imports functions
      (Map₂ (fun expression ty => global.GLOBAL ty expression) globalExpressions (globals.map globalinst.TYPE))
      (tables.map table.TABLE) (memories.map mem.MEMORY)
      (Map₃ (fun mode expressions ty => elem.ELEM ty expressions mode)
        elementModes elementExpressions (elements.map eleminst.TYPE))
      (Map₂ data.DATA (datas.map datainst.BYTES) dataModes) start exports)
    (layout : inst = ⟨types,
      importedFunctions ++ List.range' s.FUNCS.length functions.length,
      importedGlobals ++ List.range' s.GLOBALS.length globals.length,
      importedTables ++ List.range' s.TABLES.length tables.length,
      importedMemories ++ List.range' s.MEMS.length memories.length,
      List.range' s.ELEMS.length elements.length, List.range' s.DATAS.length datas.length, exportInstances⟩)
    (importFunctions : fun_funcs externals importedFunctions)
    (importGlobals : fun_globals externals importedGlobals)
    (importTables : fun_tables externals importedTables)
    (importMemories : fun_mems externals importedMemories)
    (resolvedExports : List.Forall₂ (fun ex allocated => fun_instexport inst.FUNCS inst.GLOBALS inst.TABLES inst.MEMS ex allocated)
      exports exportInstances)
    (storeWf : wf_store s) (sourceWf : wf_module source) (instanceWf : wf_moduleinst inst)
    (functionsWf : Forall wf_func functions)
    (functionBounds : ∀ function ∈ functions, allocationFunctionIndex function < inst.TYPES.length)
    (globalsWf : Forall wf_globalinst globals) (tablesWf : Forall wf_tabletype tables)
    (memoriesWf : Forall wf_memtype memories) (datasWf : Forall wf_datainst datas) :
    fun_allocmodule s source externals (globals.map globalinst.VALUE) (elements.map eleminst.REFS)
      (allocationStore s inst functions globals tables memories elements datas, inst) := by
  let s1 := {s with FUNCS := s.FUNCS ++ functions.map (allocationFunction inst)}
  let s2 := {s1 with GLOBALS := s.GLOBALS ++ globals}
  let s3 := {s2 with TABLES := s.TABLES ++ tables.map allocationTable}
  let s4 := {s3 with MEMS := s.MEMS ++ memories.map allocationMemory}
  let s5 := {s4 with ELEMS := s.ELEMS ++ elements}
  let s6 := allocationStore s inst functions globals tables memories elements datas
  have f := allocate_functions s inst functions instanceWf functionsWf functionBounds
  have g := allocate_globals s1 globals globalsWf
  have t := allocate_tables s2 tables tablesWf
  have m := allocate_memories s3 memories memoriesWf
  have e := allocate_elements s4 elements
  have d := allocate_datas s5 datas datasWf
  obtain ⟨oldFunctions, oldGlobals, oldTables, oldMemories, oldDatas⟩ := store_parts storeWf
  have newFunctions : Forall wf_funcinst (functions.map (allocationFunction inst)) := by
    intro value member
    obtain ⟨function, present, rfl⟩ := List.mem_map.mp member
    exact allocation_function_wf inst function instanceWf (functionsWf function present)
  have newTables : Forall wf_tableinst (tables.map allocationTable) := by
    intro value member
    obtain ⟨ty, present, rfl⟩ := List.mem_map.mp member
    cases ty with | mk_tabletype limits rt =>
      cases limits with | mk_limits minimum maximum =>
        cases minimum
        exact .tableinst_case_ _ _ (tablesWf _ present)
  have newMemories : Forall wf_meminst (memories.map allocationMemory) := by
    intro value member
    obtain ⟨ty, present, rfl⟩ := List.mem_map.mp member
    cases ty with | PAGE limits =>
      cases limits with | mk_limits minimum maximum =>
        cases minimum
        constructor
        · exact memoriesWf _ present
        · intro value member
          have same := (List.mem_replicate.mp member).2
          rw [same]; constructor; norm_num
  have wf1 : wf_store s1 := .store_case_ _ _ _ _ _ _ (forall_append oldFunctions newFunctions) oldGlobals oldTables oldMemories oldDatas
  have wf2 : wf_store s2 := .store_case_ _ _ _ _ _ _ (forall_append oldFunctions newFunctions) (forall_append oldGlobals globalsWf) oldTables oldMemories oldDatas
  have wf3 : wf_store s3 := .store_case_ _ _ _ _ _ _ (forall_append oldFunctions newFunctions) (forall_append oldGlobals globalsWf) (forall_append oldTables newTables) oldMemories oldDatas
  have wf4 : wf_store s4 := .store_case_ _ _ _ _ _ _ (forall_append oldFunctions newFunctions) (forall_append oldGlobals globalsWf) (forall_append oldTables newTables) (forall_append oldMemories newMemories) oldDatas
  have wf5 : wf_store s5 := .store_case_ _ _ _ _ _ _ (forall_append oldFunctions newFunctions) (forall_append oldGlobals globalsWf) (forall_append oldTables newTables) (forall_append oldMemories newMemories) oldDatas
  have wf6 : wf_store s6 := .store_case_ _ _ _ _ _ _ (forall_append oldFunctions newFunctions) (forall_append oldGlobals globalsWf) (forall_append oldTables newTables) (forall_append oldMemories newMemories) (forall_append oldDatas datasWf)
  have exportsResolved : Forall₂ (fun allocated ex => fun_instexport
      (importedFunctions ++ List.range' s.FUNCS.length functions.length)
      (importedGlobals ++ List.range' s.GLOBALS.length globals.length)
      (importedTables ++ List.range' s.TABLES.length tables.length)
      (importedMemories ++ List.range' s.MEMS.length memories.length) ex allocated) exportInstances exports := by
    intro pair member
    have proof := List.forall₂_zip resolvedExports.flip member
    simpa only [layout] using proof
  refine fun_allocmodule.fun_allocmodule_case_0 s source externals (globals.map globalinst.VALUE)
    (elements.map eleminst.REFS) s6 inst types imports functions.length functions globals.length
    globalExpressions (globals.map globalinst.TYPE) tables.length tables memories.length memories
    elements.length elementModes elementExpressions (elements.map eleminst.TYPE) datas.length
    (datas.map datainst.BYTES) dataModes start exports s1 s2 s3 s4 s5
    importedFunctions importedGlobals importedTables importedMemories
    (List.range' s.FUNCS.length functions.length) (List.range' s.GLOBALS.length globals.length)
    (List.range' s.TABLES.length tables.length) (List.range' s.MEMS.length memories.length)
    (List.range' s.ELEMS.length elements.length) (List.range' s.DATAS.length datas.length)
    exportInstances _ _ _ _ _ _ exportInstances importedMemories importedTables importedGlobals importedFunctions
    d e m t g f resolvedExports.length_eq.symm exportsResolved importMemories importTables importGlobals importFunctions
    sourceEq rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ rfl layout rfl rfl rfl rfl rfl rfl
    wf6 instanceWf wf1 wf2 wf3 wf4 wf5 ?_ ?_
  all_goals first
    | exact List.range'_eq_map_range
    | simpa only [← sourceEq, Map] using sourceWf
    | simpa only [← layout] using instanceWf
end Itasca.Runtime.Spec

end

/-! ## SplitCopy -/

section

namespace Itasca.Runtime.Spec.Segment

/-- A write in the left half of a split buffer reconstructs the corresponding
write in the original buffer. -/
theorem set_slice_split_left {T : Type} (before payload : List T) (split start : Nat)
    (splitBound : split ≤ before.length) (inside : start+payload.length ≤ split) :
    (before.take split).setSlice! start payload ++ before.drop split = before.setSlice! start payload := by
  have leftRoom : payload.length ≤ (before.take split).length-start := by simp only [List.length_take]; omega
  have wholeRoom : payload.length ≤ before.length-start := by omega
  simp only [List.setSlice!,Nat.min_eq_left leftRoom,Nat.min_eq_left wholeRoom,List.take_length]
  rw [List.take_take, Nat.min_eq_left (by omega : start ≤ split)]
  rw [List.drop_take]
  have combine := List.take_append_drop (split-(start+payload.length)) (before.drop (start+payload.length))
  rw [List.drop_drop] at combine
  have total : start+payload.length+(split-(start+payload.length))=split := by omega
  rw [total] at combine
  simpa only [List.append_assoc] using congrArg (fun rest => before.take start ++ payload ++ rest) combine

/-- A write starting at the right half reconstructs its original-buffer write. -/
theorem set_slice_split_right {T : Type} (before payload : List T) (split : Nat)
    (inside : split+payload.length ≤ before.length) :
    before.take split ++ (before.drop split).setSlice! 0 payload = before.setSlice! split payload := by
  have room : payload.length ≤ before.length-split := by omega
  simp [List.setSlice!,room,List.drop_drop,Nat.min_eq_left room,List.append_assoc]
end Itasca.Runtime.Spec.Segment

end

/-! ## PureWf -/

section

namespace Itasca.Runtime.Spec
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem pure_output_wf {before after : List admininstr} (step : Step_pure before after) :
    Forall wf_admininstr after := by
  cases step
  all_goals simp_all only [Forall,List.mem_cons,List.not_mem_nil,false_implies,implies_true,forall_eq_or_imp,true_and]
  all_goals try { solve | simp_all [wf_admininstr_val] }
  all_goals cases_type wf_admininstr
  all_goals simp_all [Forall,List.mem_append]
  all_goals simp only [Map,List.mem_map] at *
  all_goals aesop (add safe apply wf_admininstr_instr)

theorem val_wf_of_admin {value : val} (h : wf_admininstr (admininstr_val value)) :
    wf_val value := by
  cases value <;> cases h <;> constructor <;> assumption

theorem pure_singleton_wf {before : List admininstr} {value : val}
    (step : Step_pure before [admininstr_val value]) : wf_val value := by
  exact val_wf_of_admin (pure_output_wf step _ (by simp))

theorem pure_i32_bound {before : List admininstr} {n : Nat}
    (step : Step_pure before [admininstr_val (.CONST .I32 (.mk_num__0 .I32 (.mk_uN n)))]) :
    n < 2^32 := by
  have h := pure_singleton_wf step
  cases h
  cases_type wf_num_
  cases_type wf_uN
  norm_num [size,valtype_Inn] at *
  omega
end Itasca.Runtime.Spec

end

/-! ## EventfulInfinite -/

section

namespace Itasca.Runtime.Spec
open SpecExt

/-- A coherent infinite source execution retaining the events in every positive
chunk. Empty event lists remain possible for arbitrarily long executions. -/
def InfiniteSourceWithEvents (initial : config) : Prop :=
  ∃ states : Nat → config, ∃ events : Nat → List HostEvent,
    states 0 = initial ∧ ∀ n, ∃ count, 0 < count ∧
      StepsHN count (states n) (events n) (states (n+1))

theorem InfiniteSourceWithEvents.prepend {initial next : config} {events : List HostEvent}
    (infinite : InfiniteSourceWithEvents next) (steps : StepsH initial events next) :
    InfiniteSourceWithEvents initial := by
  obtain ⟨states,trace,first,edges⟩ := infinite
  obtain ⟨prefixCount,prefixSteps⟩ := steps_h_count steps
  refine ⟨(fun n => match n with | 0 => initial | n+1 => states (n+1)),
    (fun n => match n with | 0 => events ++ trace 0 | n+1 => trace (n+1)),rfl,?_⟩
  intro n
  cases n with
  | zero =>
    obtain ⟨count,positive,edge⟩ := edges 0
    rw [first] at edge
    exact ⟨prefixCount+count,by omega,by simpa using prefixSteps.trans edge⟩
  | succ n => exact edges (n+1)

/-- Conditional simulation plumbing: total concrete successors and strict
administrative decrease yield a positive source chunk with a real finite
concrete history. No fixed bound on future host-published code is assumed. -/
theorem positive_history_of_decreasing_stutter {S : Type}
    (next : S → List HostEvent → S → Prop) (decode : S → config) (potential : S → Nat)
    (successor : ∀ s, ∃ events after, next s events after)
    (simulation : ∀ s events after, next s events after →
      (decode s = decode after ∧ events = [] ∧ potential after < potential s) ∨
      ∃ count, 0 < count ∧ StepsHN count (decode s) events (decode after))
    (initial : S) :
    ∃ after events dispatches count, 0 < dispatches ∧
      Iterations next dispatches initial events after ∧ 0 < count ∧
      StepsHN count (decode initial) events (decode after) := by
  have bounded : ∀ budget s, potential s ≤ budget →
      ∃ after events dispatches count, 0 < dispatches ∧
        Iterations next dispatches s events after ∧ 0 < count ∧
        StepsHN count (decode s) events (decode after) := by
    intro budget
    induction budget with
    | zero =>
      intro s bound
      obtain ⟨events,after,edge⟩ := successor s
      rcases simulation s events after edge with ⟨same,empty,decrease⟩ | ⟨count,positive,steps⟩
      · omega
      · exact ⟨after,events,1,count,by omega,by simpa using Iterations.cons edge (.refl after),positive,steps⟩
    | succ budget ih =>
      intro s bound
      obtain ⟨events,after,edge⟩ := successor s
      rcases simulation s events after edge with ⟨same,rfl,decrease⟩ | ⟨count,positive,steps⟩
      · obtain ⟨last,trace,dispatches,count,nonempty,history,positive,steps⟩ := ih after (by omega)
        exact ⟨last,trace,dispatches+1,count,by omega,by simpa using Iterations.cons edge history,
          positive,by simpa only [same] using steps⟩
      · exact ⟨after,events,1,count,by omega,by simpa using Iterations.cons edge (.refl after),positive,steps⟩
  exact bounded (potential initial) initial (Nat.le_refl _)

/-- The infinite source chunks are backed by consecutive histories of `next`.
A runtime application must establish `successor` and `simulation` from its
actual loop; this lemma alone makes no claim about interpreter execution. -/
theorem infinite_histories_of_decreasing_stutter {S : Type}
    (next : S → List HostEvent → S → Prop) (decode : S → config) (potential : S → Nat)
    (successor : ∀ s, ∃ events after, next s events after)
    (simulation : ∀ s events after, next s events after →
      (decode s = decode after ∧ events = [] ∧ potential after < potential s) ∨
      ∃ count, 0 < count ∧ StepsHN count (decode s) events (decode after))
    (initial : S) :
    ∃ states : Nat → S, ∃ events : Nat → List HostEvent,
      states 0 = initial ∧ ∀ n, ∃ dispatches count, 0 < dispatches ∧
        Iterations next dispatches (states n) (events n) (states (n+1)) ∧
        0 < count ∧ StepsHN count (decode (states n)) (events n) (decode (states (n+1))) := by
  classical
  have advance := positive_history_of_decreasing_stutter next decode potential successor simulation
  let stateAfter (s : S) : S := Classical.choose (advance s)
  let traceAfter (s : S) : List HostEvent := Classical.choose (Classical.choose_spec (advance s))
  let states : Nat → S := fun n => Nat.rec initial (fun _ previous => stateAfter previous) n
  refine ⟨states,fun n => traceAfter (states n),rfl,?_⟩
  intro n
  exact Classical.choose_spec (Classical.choose_spec (advance (states n)))

theorem infinite_source_of_decreasing_stutter {S : Type}
    (next : S → List HostEvent → S → Prop) (decode : S → config) (potential : S → Nat)
    (successor : ∀ s, ∃ events after, next s events after)
    (simulation : ∀ s events after, next s events after →
      (decode s = decode after ∧ events = [] ∧ potential after < potential s) ∨
      ∃ count, 0 < count ∧ StepsHN count (decode s) events (decode after))
    (initial : S) : InfiniteSourceWithEvents (decode initial) := by
  obtain ⟨states,events,first,edges⟩ :=
    infinite_histories_of_decreasing_stutter next decode potential successor simulation initial
  refine ⟨fun n => decode (states n),events,congrArg decode first,?_⟩
  intro n
  obtain ⟨dispatches,count,nonempty,history,positive,steps⟩ := edges n
  exact ⟨count,positive,steps⟩
end Itasca.Runtime.Spec

end

/-! ## HostCall -/

section

namespace Itasca.Runtime.Spec
open SpecExt

/-- Typed source arguments make a host-call redex well formed. -/
theorem host_call_wf {s : store} {f : frame} {fa : funcaddr}
    {params : List valtype} {args : List val}
    (source : wf_store s) (ambient : wf_frame f) (typed : ResultsTyped s params args) :
    wf_config ⟨⟨s, f⟩, vals args ++ [.CALL_ADDR fa]⟩ := by
  apply wf_config_make source ambient
  apply forall_append (wf_vals (results_typed_wf typed))
  intro instruction member
  have same := List.mem_singleton.mp member
  subst instruction
  exact .admininstr_case_70 fa

/-- A host result that passed the concrete type check supplies the independent
host extension's result-typing premise and records the returned source values. -/
theorem host_return_step {s s' : store} {f : frame} {fa : funcaddr} {id : Nat}
    {params results : List valtype} {args returned : List val}
    (host : HostFunction s fa id params results)
    (arguments : ResultsTyped s params args) (extension : Extend_store s s')
    (sourceTyped : Store_ok s')
    (typed : ResultsTyped s' results returned) (ambient : wf_frame f) :
    StepH ⟨⟨s, f⟩, vals args ++ [.CALL_ADDR fa]⟩ [.call fa args (some returned)]
      ⟨⟨s', f⟩, vals returned⟩ := by
  have stores := extend_store_wf extension
  exact .host_return host arguments extension sourceTyped typed
    (host_call_wf stores.1 ambient arguments)
    (wf_config_vals stores.2 ambient (results_typed_wf typed))

/-- Explicit host traps and rejected host results share the same atomic source
trap transition, including all callback store effects. -/
theorem host_trap_step {s s' : store} {f : frame} {fa : funcaddr} {id : Nat}
    {params results : List valtype} {args : List val}
    (host : HostFunction s fa id params results)
    (arguments : ResultsTyped s params args) (extension : Extend_store s s')
    (sourceTyped : Store_ok s')
    (ambient : wf_frame f) :
    StepH ⟨⟨s, f⟩, vals args ++ [.CALL_ADDR fa]⟩ [.call fa args none]
      ⟨⟨s', f⟩, [.TRAP]⟩ := by
  have stores := extend_store_wf extension
  exact .host_trap host arguments extension sourceTyped (host_call_wf stores.1 ambient arguments)
    (wf_config_trap stores.2 ambient)
end Itasca.Runtime.Spec

end

/-! ## Depth -/

section

/-!
Administrative frame depth, excluding the ambient frame. Source invocation resource arguments use this nesting measure independently of runtime slots.
-/

namespace Itasca.Runtime.Spec

mutual
  /-- Number of nested administrative frames in an instruction. -/
  def instrDepth : admininstr → Nat
    | .FRAME_ _ _ body => instrsDepth body + 1
    | .LABEL_ _ _ body => instrsDepth body
    | _ => 0

  /-- Maximum frame nesting in an administrative instruction sequence. -/
  def instrsDepth : List admininstr → Nat
    | [] => 0
    | ai :: rest => max (instrDepth ai) (instrsDepth rest)
end

/-- FRAME_ nesting of a decoded configuration, excluding its ambient frame. -/
def frameDepth : config → Nat
  | .mk_config _ body => instrsDepth body

@[simp] theorem instrs_depth_nil : instrsDepth [] = 0 := rfl

@[simp] theorem instrs_depth_append (xs ys : List admininstr) :
    instrsDepth (xs ++ ys) = max (instrsDepth xs) (instrsDepth ys) := by
  induction xs with
  | nil => simp [instrsDepth]
  | cons ai rest ih => simp [instrsDepth, ih, Nat.max_assoc]

@[simp] theorem instrs_depth_singleton (ai : admininstr) :
    instrsDepth [ai] = instrDepth ai := by simp [instrsDepth]

end Itasca.Runtime.Spec

end

/-! ## ModuleMembership -/

section

/-! The per-export source judgment scopes address membership under export
iteration. In particular it has no global nonempty-namespace requirement. -/
namespace Itasca.Runtime.Spec

/-- The source repair expresses exactly well-formed export membership. -/
theorem exportinst_in_iff (addresses : List externaddr) (entry : exportinst) :
    Exportinst_in addresses entry ↔ entry.ADDR ∈ addresses ∧ wf_exportinst entry := by
  constructor
  · intro member
    cases member with
    | mk_Exportinst_in _ contains wellFormed =>
      exact ⟨List.contains_iff_mem.mp contains, wellFormed⟩
  · rintro ⟨member, wellFormed⟩
    exact .mk_Exportinst_in addresses entry (List.length_pos_of_mem member)
      (List.contains_iff_mem.mpr member) wellFormed

/-- Empty exports satisfy the generated premise even for an empty namespace. -/
theorem empty_exports_in (addresses : List externaddr) :
    Forall (Exportinst_in addresses) [] := by
  simp [Forall]

end Itasca.Runtime.Spec

end
