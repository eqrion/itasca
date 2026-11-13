import Itasca.Runtime.SourceMachine.Ownership.Extension
import Itasca.Runtime.Spec.FloatTrunc
import Itasca.Runtime.SourceMachine.Stateful.TableRead
import Itasca.Runtime.SourceMachine.Core.Trap
import Itasca.Runtime.SourceMachine.Sim.Control
import Itasca.Runtime.SourceMachine.Sim.Structured
import Itasca.Runtime.Spec.FloatPromote
import Itasca.Runtime.Spec.MemoryGrowth
import Itasca.Runtime.SourceMachine.Measure

/-!
Sections, each formerly its own module: OwnershipStore, Drops, BulkSimulation, TableMutation, FillStore, Operands, MemoryFill, MemoryTransfer, TableFill, TableSet.
-/

/-! ## OwnershipStore -/

section

namespace Itasca.Runtime.SourceMachine.Ownership
open SpecExt Itasca.Runtime.Spec Stateful

def ReferencesOwned (bounds : Bounds) (values : List ref) : Prop :=
  ∀ value ∈ values, ValueOwned bounds (val_ref value)

structure StatefulHeapOwned (bounds : Bounds) (s : store) : Prop where
  globals : GlobalsOwned bounds s
  tables : ∀ object ∈ s.TABLES, ReferencesOwned bounds object.REFS
  elements : ∀ object ∈ s.ELEMS, ReferencesOwned bounds object.REFS
  functions : s.FUNCS.length ≤ bounds.functions

structure StatefulOwned (bounds : Bounds) (s : AState) : Prop where
  values : StateOwned bounds s
  heap : StatefulHeapOwned bounds s.store

theorem StatefulOwned.core {bounds s} (owned : StatefulOwned bounds s) : CoreOwned bounds s :=
  ⟨owned.values,owned.heap.globals⟩

theorem ReferencesOwned.modify {bounds values} (owned : ReferencesOwned bounds values)
    (index : Nat) (value : ref) (allowed : ValueOwned bounds (val_ref value)) :
    ReferencesOwned bounds (values.modify index (fun _ => value)) :=
  Segment.forall_modify _ _ _ _ owned (fun _ _ => allowed)

theorem StatefulHeapOwned.metadata {bounds before after} (owned : StatefulHeapOwned bounds before)
    (globals : after.GLOBALS = before.GLOBALS) (tables : after.TABLES = before.TABLES)
    (elements : after.ELEMS = before.ELEMS) (functions : after.FUNCS = before.FUNCS) :
    StatefulHeapOwned bounds after := by
  exact ⟨by simpa only [GlobalsOwned,globals] using owned.globals,
    by simpa only [tables] using owned.tables, by simpa only [elements] using owned.elements,
    by simpa only [functions] using owned.functions⟩

theorem StatefulHeapOwned.table_set {bounds s} (owned : StatefulHeapOwned bounds s)
    (index : Nat) (object : tableinst) (references : ReferencesOwned bounds object.REFS) :
    StatefulHeapOwned bounds {s with TABLES := s.TABLES.set index object} := by
  refine ⟨owned.globals,?_,owned.elements,owned.functions⟩
  intro item member
  rcases List.mem_or_eq_of_mem_set member with member | rfl
  · exact owned.tables item member
  · exact references

theorem StatefulHeapOwned.table_write {bounds s} (owned : StatefulHeapOwned bounds s)
    (f : frame) (index position : Nat) (value : ref) (allowed : ValueOwned bounds (val_ref value)) :
    StatefulHeapOwned bounds (Segment.tableWrite s f index position value) := by
  refine ⟨owned.globals,?_,owned.elements,owned.functions⟩
  apply Segment.forall_modify _ _ _ _ owned.tables
  intro object member
  exact member.modify position value allowed

theorem StatefulHeapOwned.table_fill {bounds s} (owned : StatefulHeapOwned bounds s)
    (f : frame) (index position : Nat) (value : ref) (count : Nat)
    (allowed : ValueOwned bounds (val_ref value)) :
    StatefulHeapOwned bounds (Segment.tableFill s f index position value count) := by
  induction count generalizing s position with
  | zero => exact owned
  | succ count ih => exact ih (owned.table_write f index position value allowed) (position+1)

theorem StatefulHeapOwned.elem_drop {bounds s} (owned : StatefulHeapOwned bounds s)
    (f : frame) (index : Nat) : StatefulHeapOwned bounds (droppedElementStore s f index) := by
  refine ⟨owned.globals,owned.tables,?_,owned.functions⟩
  apply Segment.forall_modify _ _ _ _ owned.elements
  intro object member
  simp [ReferencesOwned]

theorem StatefulHeapOwned.memory_fill {bounds s} (owned : StatefulHeapOwned bounds s)
    (f : frame) (destination value count : Nat) :
    StatefulHeapOwned bounds (Segment.memoryFill s f destination value count) := by
  induction count generalizing s destination with
  | zero => exact owned
  | succ count ih =>
    exact ih (s := Segment.memoryWrite s f destination (Segment.fillByte value)) (owned.metadata rfl rfl rfl rfl) (Segment.next32 destination)

theorem StatefulHeapOwned.table_grow {bounds s} (owned : StatefulHeapOwned bounds s)
    (index : Nat) (object fresh : tableinst) (count : Nat) (value : ref)
    (member : object ∈ s.TABLES) (allowed : ValueOwned bounds (val_ref value))
    (growth : fun_growtable object count value (some fresh)) :
    StatefulHeapOwned bounds {s with TABLES := s.TABLES.set index fresh} := by
  apply owned.table_set
  cases growth with
  | fun_growtable_case_0 _ minimum maximum type refs count source size limit target freshWf oldWf targetWf =>
    subst object
    subst fresh
    have before := owned.tables _ member
    simp only [ReferencesOwned,List.mem_append,List.mem_replicate] at *
    intro reference present
    rcases present with previous | ⟨_,rfl⟩
    · exact before reference previous
    · exact allowed

theorem StatefulHeapOwned.table_init {bounds s} (owned : StatefulHeapOwned bounds s)
    (f : frame) (index elementIndex address destination source count : Nat) (object : eleminst)
    (mapped : f.MODULE.ELEMS[elementIndex]? = some address) (found : s.ELEMS[address]? = some object)
    (inside : source+count ≤ object.REFS.length) :
    StatefulHeapOwned bounds (Segment.tableInit s f index elementIndex destination source count) := by
  rw [Segment.table_init_eq]
  refine ⟨owned.globals,?_,owned.elements,owned.functions⟩
  apply Segment.forall_modify _ _ _ _ owned.tables
  intro table before
  have exactSource : fun_elem ⟨s,f⟩ (.mk_uN elementIndex) = object := by
    simp [fun_elem,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
  dsimp only
  rw [exactSource]
  exact copy_into_forall _ _ _ _ _ _ before (owned.elements object (List.mem_of_getElem? found)) inside

theorem StatefulHeapOwned.table_copy {bounds s} (owned : StatefulHeapOwned bounds s)
    (f : frame) (index sourceIndex address sourceAddress destination source count : Nat)
    (object sourceObject : tableinst)
    (mapped : f.MODULE.TABLES[index]? = some address) (sourceMapped : f.MODULE.TABLES[sourceIndex]? = some sourceAddress)
    (found : s.TABLES[address]? = some object) (sourceFound : s.TABLES[sourceAddress]? = some sourceObject)
    (inside : source+count ≤ sourceObject.REFS.length ∧ destination+count ≤ object.REFS.length) :
    StatefulHeapOwned bounds (Segment.tableCopy s f index sourceIndex destination source count) := by
  simp only [Segment.tableCopy,List.getElem!_eq_getElem?_getD,mapped,sourceMapped,found,sourceFound,Option.getD_some]
  rw [←Segment.copy_into_eq_set_slice object.REFS sourceObject.REFS destination source count inside.1 inside.2]
  apply owned.table_set
  exact copy_into_forall _ _ _ _ _ _ (owned.tables object (List.mem_of_getElem? found))
    (owned.tables sourceObject (List.mem_of_getElem? sourceFound)) inside.1

theorem StatefulHeapOwned.memory_init {bounds s} (owned : StatefulHeapOwned bounds s)
    (f : frame) (index destination source count : Nat) :
    StatefulHeapOwned bounds (Segment.memoryInit s f index destination source count) := by
  induction count generalizing s destination source with
  | zero => exact owned
  | succ count ih =>
    apply ih
    exact owned.metadata rfl rfl rfl rfl

theorem StatefulHeapOwned.memory_copy {bounds s} (owned : StatefulHeapOwned bounds s)
    (f : frame) (destination source count : Nat) :
    StatefulHeapOwned bounds (Segment.memoryCopy s f destination source count) :=
  owned.metadata rfl rfl rfl rfl

theorem StatefulHeapOwned.data_drop {bounds s} (owned : StatefulHeapOwned bounds s)
    (f : frame) (index : Nat) : StatefulHeapOwned bounds (droppedDataStore s f index) :=
  owned.metadata rfl rfl rfl rfl

end Itasca.Runtime.SourceMachine.Ownership

end

/-! ## Drops -/

section

/-!
Source data/element segment drops: store effects and typed continuation simulation.
-/

/-! ## Drop Store -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

theorem dropped_element_store_wf (s : store) (f : frame) (index : Nat)
    (wf : wf_store s) : wf_store (droppedElementStore s f index) := by
  cases s
  cases wf
  constructor <;> assumption

theorem dropped_data_store_wf (s : store) (f : frame) (index : Nat)
    (wf : wf_store s) : wf_store (droppedDataStore s f index) := by
  cases s with | MKstore funcs globals tables memories elements data =>
  cases wf with | store_case_ _ _ _ _ _ _ hf hg ht hm hd =>
  exact .store_case_ _ _ _ _ _ _ hf hg ht hm
    (Segment.forall_modify _ _ _ _ hd (fun entry _ => .datainst_case_ _ (by simp [Forall])))

theorem dropped_element_store_as_set (s : store) (f : frame) (index address : Nat)
    (object : eleminst) (mapped : f.MODULE.ELEMS[index]? = some address)
    (found : s.ELEMS[address]? = some object) :
    droppedElementStore s f index = {s with ELEMS := s.ELEMS.set address {object with REFS := []}} := by
  simp only [droppedElementStore,List.getElem!_eq_getElem?_getD,mapped,Option.getD_some]
  rw [List.modify_eq_set_getElem?]
  simp only [found]
  rfl

theorem dropped_data_store_as_set (s : store) (f : frame) (index address : Nat)
    (object : datainst) (mapped : f.MODULE.DATAS[index]? = some address)
    (found : s.DATAS[address]? = some object) :
    droppedDataStore s f index = {s with DATAS := s.DATAS.set address {object with BYTES := []}} := by
  simp only [droppedDataStore,List.getElem!_eq_getElem?_getD,mapped,Option.getD_some]
  rw [List.modify_eq_set_getElem?]
  simp only [found]
  rfl

theorem dropped_element_store_extends (s : store) (f : frame) (index address : Nat)
    (object : eleminst) (wf : wf_store s)
    (mapped : f.MODULE.ELEMS[index]? = some address) (found : s.ELEMS[address]? = some object) :
    Extend_store s (droppedElementStore s f index) := by
  have fresh := dropped_element_store_wf s f index wf
  rw [dropped_element_store_as_set s f index address object mapped found] at fresh ⊢
  apply extend_store_set_elem s address _ wf fresh
  intro bound
  simp only [List.getElem!_eq_getElem?_getD,found,Option.getD_some]
  cases object
  exact .mk_Extend_eleminst _ _ _ (Or.inr rfl)

theorem dropped_data_store_extends (s : store) (f : frame) (index address : Nat)
    (object : datainst) (wf : wf_store s)
    (mapped : f.MODULE.DATAS[index]? = some address) (found : s.DATAS[address]? = some object) :
    Extend_store s (droppedDataStore s f index) := by
  have fresh := dropped_data_store_wf s f index wf
  rw [dropped_data_store_as_set s f index address object mapped found] at fresh ⊢
  apply extend_store_set_data s address _ wf fresh
  intro bound
  have old : wf_datainst object := by cases wf; apply_assumption; exact List.mem_of_getElem? found
  simp only [List.getElem!_eq_getElem?_getD,found,Option.getD_some]
  cases object
  exact .mk_Extend_datainst _ _ (Or.inr rfl) old (.datainst_case_ _ (by simp [Forall]))

theorem dropped_element_store_contents (s : store) (f : frame) (index : Nat)
    (contents : StoreContentsTyped s) (extension : Extend_store s (droppedElementStore s f index)) :
    StoreContentsTyped (droppedElementStore s f index) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact fun object member => globalinst_typed_extend extension (contents.globals object member)
  · exact fun object member => tableinst_typed_extend extension (contents.tables object member)
  · exact fun object member => meminst_typed_extend extension (contents.memories object member)
  · change Forall (fun object => Eleminst_ok _ object object.TYPE) (s.ELEMS.modify _ _)
    apply Segment.forall_modify
    · exact fun object member => eleminst_ok_extend extension (extend_elem_refl object) (contents.elements object member)
    · intro object typed
      cases typed with
      | mk_Eleminst_ok type refs refsOk length wf =>
        exact .mk_Eleminst_ok _ _ [] (by simp [Forall]) (by norm_num) wf
  · intro object member
    have typed := contents.data object member
    have wf : wf_datainst object := by cases typed; assumption
    exact datainst_ok_extend extension (extend_data_refl object wf) typed

theorem dropped_data_store_contents (s : store) (f : frame) (index : Nat)
    (contents : StoreContentsTyped s) (extension : Extend_store s (droppedDataStore s f index)) :
    StoreContentsTyped (droppedDataStore s f index) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact fun object member => globalinst_typed_extend extension (contents.globals object member)
  · exact fun object member => tableinst_typed_extend extension (contents.tables object member)
  · exact fun object member => meminst_typed_extend extension (contents.memories object member)
  · exact fun object member => eleminst_ok_extend extension (extend_elem_refl object) (contents.elements object member)
  · change Forall (fun object => Datainst_ok _ object .OK) (s.DATAS.modify _ _)
    apply Segment.forall_modify
    · intro object member
      have typed := contents.data object member
      have wf : wf_datainst object := by cases typed; assumption
      exact datainst_ok_extend extension (extend_data_refl object wf) typed
    · intro object typed
      exact .mk_Datainst_ok _ [] (by norm_num) (extend_store_wf extension).2 (.datainst_case_ _ (by simp [Forall]))
end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## Drops -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

def elementDrop (s : AState) (f : AFrame) (rest : List AFrame) (index : Nat) (after : List instr) : AResult :=
  match f.module.ELEMS[index]? with
  | none => .stuck
  | some address => match s.store.ELEMS[address]? with
    | none => .stuck
    | some _ => advance {s with store := droppedElementStore s.store f.toFrame index} {f with code := after} rest

theorem element_drop_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .ELEM_DROP (.mk_uN index) :: after} :: rest,[]⟩) :
    ∃ next, elementDrop ⟨s,ambient,{f with code := .ELEM_DROP (.mk_uN index) :: after} :: rest,[]⟩ f rest index after = .next next ∧
      CoreTyped next ∧ Extend_store s next.store ∧
      NextSim ⟨s,ambient,{f with code := .ELEM_DROP (.mk_uN index) :: after} :: rest,[]⟩ next := by
  have hf : FrameTyped s {f with code := .ELEM_DROP (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | elem_drop _ _ type present selected contextWf instructionWf =>
    have right : index < C.ELEMS.length := present
    have left : index < f.module.ELEMS.length := by rw [bindings.elems.length_eq]; exact right
    obtain ⟨object,found,objectTyped⟩ := bindings.elems.get left right
    simp only [List.get_eq_getElem] at found objectTyped
    have mapped : f.module.ELEMS[index]? = some f.module.ELEMS[index] := List.getElem?_eq_getElem left
    cases operandTypes
    have extension := dropped_element_store_extends s f.toFrame index f.module.ELEMS[index] object typed.typed.store mapped found
    have contents := dropped_element_store_contents s f.toFrame index typed.contents extension
    have frameNext := continuation [] .nil
    have actualFrame : FrameTyped s {f with code := after} [] := by
      simpa only [List.append_nil,←split] using frameNext
    have fresh := (active_frame_preservation typed.typed actualFrame rfl).extend_same extension rfl
    refine ⟨_,by simp only [elementDrop,mapped,found,advance],⟨fresh,contents⟩,extension,NextSim.single ?_⟩
    obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf hf
    have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
    have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
    have bound : index < 2^32 := by
      cases instructionWf with | instr_case_55 _ valid =>
      cases valid with | uN_case_0 _ valid => norm_num at valid ⊢; omega
    have source := element_drop_step s f.toFrame index typed.typed.store frameWf bound left (extend_store_wf extension).2
    have height : ∀ label ∈ f.labels, label.height ≤ f.vals.length := by simpa only [split,List.append_nil] using heights
    have full := mutable_stack_simulation s (droppedElementStore s f.toFrame index) ambient f rest (.ELEM_DROP (.mk_uN index)) after f.vals [] []
      typed.typed.ambient labelsWf valuesWf tailWf restWf height (by simpa [vals,admininstr_instr] using source)
    simpa only [List.append_nil] using full

def dataDrop (s : AState) (f : AFrame) (rest : List AFrame) (index : Nat) (after : List instr) : AResult :=
  match f.module.DATAS[index]? with
  | none => .stuck
  | some address => match s.store.DATAS[address]? with
    | none => .stuck
    | some _ => advance {s with store := droppedDataStore s.store f.toFrame index} {f with code := after} rest

theorem data_drop_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .DATA_DROP (.mk_uN index) :: after} :: rest,[]⟩) :
    ∃ next, dataDrop ⟨s,ambient,{f with code := .DATA_DROP (.mk_uN index) :: after} :: rest,[]⟩ f rest index after = .next next ∧
      CoreTyped next ∧ Extend_store s next.store ∧
      NextSim ⟨s,ambient,{f with code := .DATA_DROP (.mk_uN index) :: after} :: rest,[]⟩ next := by
  have hf : FrameTyped s {f with code := .DATA_DROP (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | data_drop _ _ present selected contextWf instructionWf =>
    have right : index < C.DATAS.length := present
    have left : index < f.module.DATAS.length := by rw [bindings.datas.length_eq]; exact right
    obtain ⟨object,found,objectTyped⟩ := bindings.datas.get left right
    simp only [List.get_eq_getElem] at found objectTyped
    have mapped : f.module.DATAS[index]? = some f.module.DATAS[index] := List.getElem?_eq_getElem left
    cases operandTypes
    have extension := dropped_data_store_extends s f.toFrame index f.module.DATAS[index] object typed.typed.store mapped found
    have contents := dropped_data_store_contents s f.toFrame index typed.contents extension
    have frameNext := continuation [] .nil
    have actualFrame : FrameTyped s {f with code := after} [] := by
      simpa only [List.append_nil,←split] using frameNext
    have fresh := (active_frame_preservation typed.typed actualFrame rfl).extend_same extension rfl
    refine ⟨_,by simp only [dataDrop,mapped,found,advance],⟨fresh,contents⟩,extension,NextSim.single ?_⟩
    obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf hf
    have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
    have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
    have bound : index < 2^32 := by
      cases instructionWf with | instr_case_67 _ valid =>
      cases valid with | uN_case_0 _ valid => norm_num at valid ⊢; omega
    have source := data_drop_step s f.toFrame index typed.typed.store frameWf bound left (extend_store_wf extension).2
    have height : ∀ label ∈ f.labels, label.height ≤ f.vals.length := by simpa only [split,List.append_nil] using heights
    have full := mutable_stack_simulation s (droppedDataStore s f.toFrame index) ambient f rest (.DATA_DROP (.mk_uN index)) after f.vals [] []
      typed.typed.ambient labelsWf valuesWf tailWf restWf height (by simpa [vals,admininstr_instr] using source)
    simpa only [List.append_nil] using full

end Itasca.Runtime.SourceMachine.Stateful

end

end

/-! ## BulkSimulation -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

theorem mutable_counted_simulation (before afterStore : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (instruction : instr) (after : List instr)
    (baseValues consumed produced : List val) (count : Nat)
    (ha : wf_frame ambient) (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (step : StepsHN count ⟨⟨before,f.toFrame⟩,vals consumed ++ [admininstr_instr instruction]⟩ []
      ⟨⟨afterStore,f.toFrame⟩,vals produced⟩) :
    StepsHN count (decode ⟨before,ambient,{f with code := instruction::after,vals := baseValues++consumed}::rest,[]⟩) []
      (decode ⟨afterStore,ambient,{f with code := after,vals := baseValues++produced}::rest,[]⟩) := by
  have first := steps_hn_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have second := steps_hn_decode_labels first f.labels baseValues hl hv
  have third := steps_hn_frame second f.arity (activeFrame ambient rest) (active_frame_wf ha hr)
  have full := steps_hn_decode_frames ambient rest third ha hr
  simp only [decode,decodeFrames,vals,List.map_nil,List.nil_append,List.map_cons,AFrame.toFrame,AFrame.arity]
  rw [decode_labels_move_values _ _ _ _ heights,decode_labels_move_values _ _ _ _ heights]
  simpa [instrContext,frameContext,vals,List.append_assoc,AFrame.arity,AFrame.toFrame] using full

/-- Every bulk operation reduces its redex at least once, including zero-length
operations. Wrapping it in source control contexts retains that positive count. -/
theorem bulk_empty_simulation (before afterStore : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (instruction : instr) (after : List instr) (baseValues consumed : List val)
    (ha : wf_frame ambient) (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (steps : StepsH ⟨⟨before,f.toFrame⟩,vals consumed ++ [admininstr_instr instruction]⟩ []
      ⟨⟨afterStore,f.toFrame⟩,[]⟩) :
    NextSim ⟨before,ambient,{f with code := instruction::after,vals := baseValues++consumed}::rest,[]⟩
      ⟨afterStore,ambient,{f with code := after,vals := baseValues}::rest,[]⟩ := by
  obtain ⟨count,trace⟩ := steps_h_count steps
  have positive : 0 < count := by
    by_contra no
    have zero : count=0 := by omega
    rw [zero] at trace
    have same := trace.zero.1
    have lengths := congrArg (fun | config.mk_config _ code => code.length) same
    simp only [List.length_append,List.length_singleton,List.length_nil] at lengths
    omega
  have full := mutable_counted_simulation before afterStore ambient f rest instruction after baseValues consumed [] count
    ha hl hv hc hr heights trace
  apply NextSim.counted (n:=count) _ positive
  simpa only [List.append_nil] using full
end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## TableMutation -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

theorem table_write_as_set (s : store) (f : frame) (index address position : Nat)
    (object : tableinst) (value : ref) (mapped : f.MODULE.TABLES[index]? = some address)
    (found : s.TABLES[address]? = some object) :
    Segment.tableWrite s f index position value =
      {s with TABLES := s.TABLES.set address {object with REFS := object.REFS.modify position (fun _ => value)}} := by
  simp only [Segment.tableWrite,List.getElem!_eq_getElem?_getD,mapped,Option.getD_some]
  rw [List.modify_eq_set_getElem?]
  simp only [found]
  rfl

theorem table_write_extends (s : store) (f : frame) (index address position : Nat)
    (object : tableinst) (value : ref) (wf : wf_store s) (contents : StoreContentsTyped s)
    (mapped : f.MODULE.TABLES[index]? = some address) (found : s.TABLES[address]? = some object) :
    Extend_store s (Segment.tableWrite s f index position value) := by
  have fresh := Segment.table_write_wf s f index position value wf
  rw [table_write_as_set s f index address position object value mapped found] at fresh ⊢
  apply extend_store_set_table s address _ wf fresh
  intro bound
  simp only [List.getElem!_eq_getElem?_getD,found,Option.getD_some]
  have typed := contents.tables object (List.mem_of_getElem? found)
  cases typed with
  | mk_Tableinst_ok count maximum type refs typeOk refsOk length _ oldWf typeWf =>
    exact extend_table_contents count count maximum type refs (refs.modify position (fun _ => value))
      (by rfl) (by simp) oldWf (.tableinst_case_ _ _ typeWf)

theorem table_write_contents (s : store) (f : frame) (index address position : Nat)
    (object : tableinst) (value : ref) (wf : wf_store s) (contents : StoreContentsTyped s)
    (mapped : f.MODULE.TABLES[index]? = some address) (found : s.TABLES[address]? = some object)
    (valueTyped : Ref_ok s value (tableElementType object.TYPE)) :
    StoreContentsTyped (Segment.tableWrite s f index position value) := by
  have extension := table_write_extends s f index address position object value wf contents mapped found
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact fun item member => globalinst_typed_extend extension (contents.globals item member)
  · intro item member
    have objects := congrArg store.TABLES (table_write_as_set s f index address position object value mapped found)
    rw [objects] at member
    rcases List.mem_or_eq_of_mem_set member with member | rfl
    · exact tableinst_typed_extend extension (contents.tables item member)
    · have typed := contents.tables object (List.mem_of_getElem? found)
      cases typed with
      | mk_Tableinst_ok count maximum type refs typeOk refsOk length _ oldWf typeWf =>
        apply Tableinst_ok.mk_Tableinst_ok _ count maximum type (refs.modify position (fun _ => value)) typeOk
        · apply Segment.forall_modify
          · exact fun reference member => ref_ok_extend extension (refsOk reference member)
          · intro reference _
            exact ref_ok_extend extension valueTyped
        · simpa only [List.length_modify] using length
        · exact (extend_store_wf extension).2
        · exact .tableinst_case_ _ _ typeWf
        · exact typeWf
  · exact fun item member => meminst_typed_extend extension (contents.memories item member)
  · exact fun item member => eleminst_ok_extend extension (extend_elem_refl item) (contents.elements item member)
  · intro item member
    have typed := contents.data item member
    have itemWf : wf_datainst item := by cases typed; assumption
    exact datainst_ok_extend extension (extend_data_refl item itemWf) typed
end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## FillStore -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

theorem table_fill_preserves (s : store) (f : frame) (index address destination : Nat)
    (object : tableinst) (value : ref) (count : Nat) (wf : wf_store s) (contents : StoreContentsTyped s)
    (mapped : f.MODULE.TABLES[index]? = some address) (found : s.TABLES[address]? = some object)
    (valueTyped : Ref_ok s value (tableElementType object.TYPE)) :
    Extend_store s (Segment.tableFill s f index destination value count) ∧
      StoreContentsTyped (Segment.tableFill s f index destination value count) ∧
      (Segment.tableFill s f index destination value count).FUNCS = s.FUNCS := by
  induction count generalizing s object destination with
  | zero => exact ⟨extend_store_refl s wf,contents,rfl⟩
  | succ count ih =>
    have extension := table_write_extends s f index address destination object value wf contents mapped found
    have fresh := table_write_contents s f index address destination object value wf contents mapped found valueTyped
    have lookup : (Segment.tableWrite s f index destination value).TABLES[address]? =
        some {object with REFS := object.REFS.modify destination (fun _ => value)} := by
      rw [table_write_as_set s f index address destination object value mapped found]
      simp only [List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1]
    have valueFresh := ref_ok_extend extension valueTyped
    obtain ⟨later,typed,functions⟩ := ih (Segment.tableWrite s f index destination value)
      (destination+1) {object with REFS := object.REFS.modify destination (fun _ => value)}
      (extend_store_wf extension).2 fresh lookup valueFresh
    exact ⟨extend_store_trans extension later,typed,functions⟩

theorem memory_write_as_payload (s : store) (f : frame) (position : Nat) (value : byte) :
    Segment.memoryWrite s f position value = memoryPayloadWrite s f position [value] := by
  simp only [Segment.memoryWrite,memoryPayloadWrite,Segment.splice_singleton_eq_set]

theorem memory_fill_preserves (s : store) (f : frame) (address destination value count : Nat)
    (object : meminst) (wf : wf_store s) (contents : StoreContentsTyped s)
    (mapped : f.MODULE.MEMS[0]? = some address) (found : s.MEMS[address]? = some object) :
    Extend_store s (Segment.memoryFill s f destination value count) ∧
      StoreContentsTyped (Segment.memoryFill s f destination value count) ∧
      (Segment.memoryFill s f destination value count).FUNCS = s.FUNCS := by
  induction count generalizing s object destination with
  | zero => exact ⟨extend_store_refl s wf,contents,rfl⟩
  | succ count ih =>
    have byteWf : Forall wf_byte [Segment.fillByte value] := by simpa [Forall] using Segment.fill_byte_wf value
    have extension := memory_payload_write_extends s f address destination object [Segment.fillByte value] wf contents mapped found byteWf
    have fresh := contents.memory_write wf f address destination object [Segment.fillByte value] mapped found byteWf
    rw [←memory_write_as_payload] at extension fresh
    have lookup : (Segment.memoryWrite s f destination (Segment.fillByte value)).MEMS[address]? =
        some {object with BYTES := object.BYTES.set destination (Segment.fillByte value)} := by
      rw [memory_write_as_payload,memory_payload_write_as_set s f address destination object _ mapped found,Segment.splice_singleton_eq_set]
      simp only [List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1]
    obtain ⟨later,typed,functions⟩ := ih (Segment.memoryWrite s f destination (Segment.fillByte value))
      (Segment.next32 destination) {object with BYTES := object.BYTES.set destination (Segment.fillByte value)}
      (extend_store_wf extension).2 fresh lookup
    exact ⟨extend_store_trans extension later,typed,functions⟩
end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## Operands -/

section

namespace Itasca.Runtime.SourceMachine.Stateful

def popThree (values : List val) : Option (List val × val × val × val) :=
  match pop values with
  | none => none
  | some (first,c) => match pop first with
    | none => none
    | some (second,b) => match pop second with
      | none => none
      | some (front,a) => some (front,a,b,c)

@[simp] theorem pop_three_append (front : List val) (a b c : val) :
    popThree (front ++ [a,b,c]) = some (front,a,b,c) := by
  have split : front ++ [a,b,c] = ((front ++ [a]) ++ [b]) ++ [c] := by simp [List.append_assoc]
  simp only [popThree,split,pop_append]
end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## MemoryFill -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

def memoryFill (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr) : AResult :=
  match popThree f.vals, f.module.MEMS[0]? with
  | some (front,offset,value,size), some address =>
    match integer .I32 offset, integer .I32 value, integer .I32 size, s.store.MEMS[address]? with
    | some destination, some valueNumber, some count, some object =>
      if destination+count ≤ object.BYTES.length then
        advance {s with store := Segment.memoryFill s.store f.toFrame destination valueNumber count}
          {f with code := after,vals := front} rest
      else .trap
    | _,_,_,_ => .stuck
  | _,_ => .stuck

theorem memory_fill_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .MEMORY_FILL::after}::rest,[]⟩) :
    (∃ next, memoryFill ⟨s,ambient,{f with code := .MEMORY_FILL::after}::rest,[]⟩ f rest after = .next next ∧
      CoreTyped next ∧ Extend_store s next.store ∧
      NextSim ⟨s,ambient,{f with code := .MEMORY_FILL::after}::rest,[]⟩ next) ∨
    (memoryFill ⟨s,ambient,{f with code := .MEMORY_FILL::after}::rest,[]⟩ f rest after = .trap ∧
      ∃ count,0<count ∧ StepsHN count (decode ⟨s,ambient,{f with code := .MEMORY_FILL::after}::rest,[]⟩) []
        ⟨⟨s,ambient⟩,[.TRAP]⟩) := by
  have hf : FrameTyped s {f with code := .MEMORY_FILL::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | memory_fill _ type present selected contextWf typeWf instructionWf =>
    obtain ⟨address,object,mapped,found⟩ := bindings.memory_lookup present
    cases operandTypes with
    | cons destinationTyped tail => cases tail with
      | cons valueTyped tail => cases tail with
        | cons countTyped tail =>
          cases tail
          obtain ⟨destination,rfl,destinationBound⟩ := integer_val_inv (ty:=.I32) destinationTyped
          obtain ⟨valueNumber,rfl,valueBound⟩ := integer_val_inv (ty:=.I32) valueTyped
          obtain ⟨count,rfl,countBound⟩ := integer_val_inv (ty:=.I32) countTyped
          have destinationDecoded := integer_accepts .I32 destination destinationBound
          have countDecoded := integer_accepts .I32 count countBound
          simp only [numtype_Inn] at destinationDecoded countDecoded
          have valueDecoded := integer_accepts .I32 valueNumber valueBound
          simp only [numtype_Inn] at valueDecoded
          obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf hf
          have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
          have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
          have memoryEq : fun_mem ⟨s,f.toFrame⟩ (.mk_uN 0) = object := by
            simp [fun_mem,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
          by_cases inside : destination+count ≤ object.BYTES.length
          · obtain ⟨extension,contents,functions⟩ := memory_fill_preserves s f.toFrame address destination valueNumber count object
              typed.typed.store typed.contents mapped found
            have frameNext : FrameTyped s {f with code:=after,vals:=front} [] := by
              simpa only [List.append_nil] using continuation [] .nil
            have fresh := (active_frame_preservation typed.typed frameNext rfl).extend_same extension functions
            apply Or.inl
            refine ⟨_,by simp only [memoryFill,split,pop_three_append,mapped,destinationDecoded,valueDecoded,countDecoded,found,inside,ite_true,advance],
              ⟨fresh,contents⟩,extension,?_⟩
            have addressBound : f.module.MEMS[0]! < s.MEMS.length := by
              simp only [List.getElem!_eq_getElem?_getD,mapped,Option.getD_some]
              exact (List.getElem?_eq_some_iff.mp found).1
            have source := Segment.memory_fill_steps s f.toFrame destination valueNumber count typed.typed.store frameWf
              destinationBound valueBound countBound (List.getElem?_eq_some_iff.mp mapped).1 addressBound
              (by simpa only [memoryEq] using inside)
            have full := bulk_empty_simulation s (Segment.memoryFill s f.toFrame destination valueNumber count) ambient f rest
              (.MEMORY_FILL) after front [integerVal .I32 destination,integerVal .I32 valueNumber,integerVal .I32 count]
              typed.typed.ambient labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.operands,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
            simpa only [split] using full
          · apply Or.inr
            refine ⟨by simp only [memoryFill,split,pop_three_append,mapped,destinationDecoded,valueDecoded,countDecoded,found,inside,ite_false],?_⟩
            have source := Segment.memory_fill_trap s f.toFrame destination valueNumber count typed.typed.store frameWf
              destinationBound valueBound countBound (by simpa only [memoryEq] using Nat.lt_of_not_ge inside)
            have full := operand_trap_simulation s ambient f rest (.MEMORY_FILL) after front
              [integerVal .I32 destination,integerVal .I32 valueNumber,integerVal .I32 count] typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.operands,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
            simpa only [split] using full
end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## MemoryTransfer -/

section

/-!
Source memory copy and initialization, retaining their distinct segment/snapshot premises while sharing bounded transfer simulation.
-/

/-! ## Memory Copy -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

def memoryCopy (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr) : AResult :=
  match popThree f.vals, f.module.MEMS[0]? with
  | some (front,offset,value,size), some address =>
    match integer .I32 offset, integer .I32 value, integer .I32 size, s.store.MEMS[address]? with
    | some destination, some sourceOffset, some count, some object =>
      if sourceOffset+count ≤ object.BYTES.length ∧ destination+count ≤ object.BYTES.length then
        advance {s with store := Segment.memoryCopy s.store f.toFrame destination sourceOffset count}
          {f with code := after,vals := front} rest
      else .trap
    | _,_,_,_ => .stuck
  | _,_ => .stuck

theorem memory_copy_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .MEMORY_COPY::after}::rest,[]⟩) :
    (∃ next, memoryCopy ⟨s,ambient,{f with code := .MEMORY_COPY::after}::rest,[]⟩ f rest after = .next next ∧
      CoreTyped next ∧ Extend_store s next.store ∧
      NextSim ⟨s,ambient,{f with code := .MEMORY_COPY::after}::rest,[]⟩ next) ∨
    (memoryCopy ⟨s,ambient,{f with code := .MEMORY_COPY::after}::rest,[]⟩ f rest after = .trap ∧
      ∃ count,0<count ∧ StepsHN count (decode ⟨s,ambient,{f with code := .MEMORY_COPY::after}::rest,[]⟩) []
        ⟨⟨s,ambient⟩,[.TRAP]⟩) := by
  have hf : FrameTyped s {f with code := .MEMORY_COPY::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | memory_copy _ type present selected contextWf typeWf instructionWf =>
    obtain ⟨address,object,mapped,found⟩ := bindings.memory_lookup present
    cases operandTypes with
    | cons destinationTyped tail => cases tail with
      | cons valueTyped tail => cases tail with
        | cons countTyped tail =>
          cases tail
          obtain ⟨destination,rfl,destinationBound⟩ := integer_val_inv (ty:=.I32) destinationTyped
          obtain ⟨sourceOffset,rfl,valueBound⟩ := integer_val_inv (ty:=.I32) valueTyped
          obtain ⟨count,rfl,countBound⟩ := integer_val_inv (ty:=.I32) countTyped
          have destinationDecoded := integer_accepts .I32 destination destinationBound
          have countDecoded := integer_accepts .I32 count countBound
          simp only [numtype_Inn] at destinationDecoded countDecoded
          have valueDecoded := integer_accepts .I32 sourceOffset valueBound
          simp only [numtype_Inn] at valueDecoded
          obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf hf
          have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
          have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
          have memoryEq : fun_mem ⟨s,f.toFrame⟩ (.mk_uN 0) = object := by
            simp [fun_mem,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
          by_cases inside : sourceOffset+count ≤ object.BYTES.length ∧ destination+count ≤ object.BYTES.length
          · obtain ⟨extension,contents⟩ := memory_copy_preserves s f.toFrame address destination sourceOffset count object
              typed.typed.store typed.contents mapped found inside
            have frameNext : FrameTyped s {f with code:=after,vals:=front} [] := by
              simpa only [List.append_nil] using continuation [] .nil
            have fresh := (active_frame_preservation typed.typed frameNext rfl).extend_same extension rfl
            apply Or.inl
            refine ⟨_,by simp only [memoryCopy,split,pop_three_append,mapped,destinationDecoded,valueDecoded,countDecoded,found,inside,and_true,ite_true,advance],
              ⟨fresh,contents⟩,extension,?_⟩
            have addressBound : f.module.MEMS[0]! < s.MEMS.length := by
              simp only [List.getElem!_eq_getElem?_getD,mapped,Option.getD_some]
              exact (List.getElem?_eq_some_iff.mp found).1
            have source := Segment.memory_copy_steps s f.toFrame destination sourceOffset count typed.typed.store frameWf
              destinationBound valueBound countBound (List.getElem?_eq_some_iff.mp mapped).1 addressBound
              (by rw [memoryEq]; exact memory_byte_length_bound typed.contents (List.mem_of_getElem? found))
              (by simpa only [memoryEq] using inside)
            have full := bulk_empty_simulation s (Segment.memoryCopy s f.toFrame destination sourceOffset count) ambient f rest
              (.MEMORY_COPY) after front [integerVal .I32 destination,integerVal .I32 sourceOffset,integerVal .I32 count]
              typed.typed.ambient labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.operands,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
            simpa only [split] using full
          · apply Or.inr
            refine ⟨by simp only [memoryCopy,split,pop_three_append,mapped,destinationDecoded,valueDecoded,countDecoded,found,inside,ite_false],?_⟩
            have source := Segment.memory_copy_trap s f.toFrame destination sourceOffset count typed.typed.store frameWf
              destinationBound valueBound countBound (by rw [memoryEq]; omega)
            have full := operand_trap_simulation s ambient f rest (.MEMORY_COPY) after front
              [integerVal .I32 destination,integerVal .I32 sourceOffset,integerVal .I32 count] typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.operands,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
            simpa only [split] using full
end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## Memory Init -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

def memoryInit (s : AState) (f : AFrame) (rest : List AFrame) (dataIndex : Nat) (after : List instr) : AResult :=
  match popThree f.vals, f.module.MEMS[0]?, f.module.DATAS[dataIndex]? with
  | some (front,offset,value,size), some address, some dataAddress =>
    match integer .I32 offset, integer .I32 value, integer .I32 size, s.store.MEMS[address]?, s.store.DATAS[dataAddress]? with
    | some destination, some sourceOffset, some count, some object, some data =>
      if sourceOffset+count ≤ data.BYTES.length ∧ destination+count ≤ object.BYTES.length then
        advance {s with store := Segment.memoryInit s.store f.toFrame dataIndex destination sourceOffset count}
          {f with code := after,vals := front} rest
      else .trap
    | _,_,_,_,_ => .stuck
  | _,_,_ => .stuck

theorem memory_init_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (dataIndex : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .MEMORY_INIT (.mk_uN dataIndex)::after}::rest,[]⟩) :
    (∃ next, memoryInit ⟨s,ambient,{f with code := .MEMORY_INIT (.mk_uN dataIndex)::after}::rest,[]⟩ f rest dataIndex after = .next next ∧
      CoreTyped next ∧ Extend_store s next.store ∧
      NextSim ⟨s,ambient,{f with code := .MEMORY_INIT (.mk_uN dataIndex)::after}::rest,[]⟩ next) ∨
    (memoryInit ⟨s,ambient,{f with code := .MEMORY_INIT (.mk_uN dataIndex)::after}::rest,[]⟩ f rest dataIndex after = .trap ∧
      ∃ count,0<count ∧ StepsHN count (decode ⟨s,ambient,{f with code := .MEMORY_INIT (.mk_uN dataIndex)::after}::rest,[]⟩) []
        ⟨⟨s,ambient⟩,[.TRAP]⟩) := by
  have hf : FrameTyped s {f with code := .MEMORY_INIT (.mk_uN dataIndex)::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | memory_init _ _ type present selected dataPresent dataSelected contextWf typeWf instructionWf =>
    obtain ⟨address,object,mapped,found⟩ := bindings.memory_lookup present
    have dataLeft : dataIndex < f.module.DATAS.length := by rw [bindings.datas.length_eq]; exact dataPresent
    obtain ⟨data,dataFound,dataTyped⟩ := bindings.datas.get dataLeft dataPresent
    simp only [List.get_eq_getElem] at dataFound dataTyped
    have dataMapped : f.module.DATAS[dataIndex]? = some f.module.DATAS[dataIndex] := List.getElem?_eq_getElem dataLeft
    obtain ⟨dataBound,dataBytes⟩ := data_bytes_typed (typed.contents.data data (List.mem_of_getElem? dataFound))
    cases operandTypes with
    | cons destinationTyped tail => cases tail with
      | cons valueTyped tail => cases tail with
        | cons countTyped tail =>
          cases tail
          obtain ⟨destination,rfl,destinationBound⟩ := integer_val_inv (ty:=.I32) destinationTyped
          obtain ⟨sourceOffset,rfl,valueBound⟩ := integer_val_inv (ty:=.I32) valueTyped
          obtain ⟨count,rfl,countBound⟩ := integer_val_inv (ty:=.I32) countTyped
          have destinationDecoded := integer_accepts .I32 destination destinationBound
          have countDecoded := integer_accepts .I32 count countBound
          simp only [numtype_Inn] at destinationDecoded countDecoded
          have valueDecoded := integer_accepts .I32 sourceOffset valueBound
          simp only [numtype_Inn] at valueDecoded
          obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf hf
          have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
          have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
          have memoryEq : fun_mem ⟨s,f.toFrame⟩ (.mk_uN 0) = object := by
            simp [fun_mem,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
          have dataIndexBound : dataIndex<2^32 := by cases instructionWf; rename_i valid; cases valid; norm_num at *; omega
          have dataEq : fun_data ⟨s,f.toFrame⟩ (.mk_uN dataIndex) = data := by
            simp [fun_data,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,dataMapped,dataFound]
          by_cases inside : sourceOffset+count ≤ data.BYTES.length ∧ destination+count ≤ object.BYTES.length
          · obtain ⟨extension,contents,functions⟩ := memory_init_preserves s f.toFrame address dataIndex f.module.DATAS[dataIndex] destination sourceOffset count object data
              typed.typed.store typed.contents mapped found dataMapped dataFound inside
            have frameNext : FrameTyped s {f with code:=after,vals:=front} [] := by
              simpa only [List.append_nil] using continuation [] .nil
            have fresh := (active_frame_preservation typed.typed frameNext rfl).extend_same extension functions
            apply Or.inl
            refine ⟨_,by simp only [memoryInit,split,pop_three_append,mapped,dataMapped,destinationDecoded,valueDecoded,countDecoded,found,dataFound,inside,and_true,ite_true,advance],
              ⟨fresh,contents⟩,extension,?_⟩
            have addressBound : f.module.MEMS[0]! < s.MEMS.length := by
              simp only [List.getElem!_eq_getElem?_getD,mapped,Option.getD_some]
              exact (List.getElem?_eq_some_iff.mp found).1
            have source := Segment.memory_init_steps s f.toFrame destination sourceOffset count dataIndex typed.typed.store frameWf
              destinationBound valueBound countBound dataIndexBound (List.getElem?_eq_some_iff.mp mapped).1 addressBound
              (by simpa only [dataEq] using dataBytes) (by simpa only [memoryEq,dataEq] using inside)
            have full := bulk_empty_simulation s (Segment.memoryInit s f.toFrame dataIndex destination sourceOffset count) ambient f rest
              (.MEMORY_INIT (.mk_uN dataIndex)) after front [integerVal .I32 destination,integerVal .I32 sourceOffset,integerVal .I32 count]
              typed.typed.ambient labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.operands,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
            simpa only [split] using full
          · apply Or.inr
            refine ⟨by simp only [memoryInit,split,pop_three_append,mapped,dataMapped,destinationDecoded,valueDecoded,countDecoded,found,dataFound,inside,ite_false],?_⟩
            have source := Segment.memory_init_trap s f.toFrame destination sourceOffset count dataIndex typed.typed.store frameWf
              destinationBound valueBound countBound dataIndexBound (by rw [memoryEq,dataEq]; omega)
            have full := operand_trap_simulation s ambient f rest (.MEMORY_INIT (.mk_uN dataIndex)) after front
              [integerVal .I32 destination,integerVal .I32 sourceOffset,integerVal .I32 count] typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.operands,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
            simpa only [split] using full
end Itasca.Runtime.SourceMachine.Stateful

end

end

/-! ## TableFill -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

def tableFill (s : AState) (f : AFrame) (rest : List AFrame) (index : Nat) (after : List instr) : AResult :=
  match popThree f.vals, f.module.TABLES[index]? with
  | some (front,offset,value,size), some address =>
    match integer .I32 offset, asReference value, integer .I32 size, s.store.TABLES[address]? with
    | some destination, some reference, some count, some object =>
      if destination+count ≤ object.REFS.length then
        advance {s with store := Segment.tableFill s.store f.toFrame index destination reference count}
          {f with code := after,vals := front} rest
      else .trap
    | _,_,_,_ => .stuck
  | _,_ => .stuck

theorem table_fill_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .TABLE_FILL (.mk_uN index)::after}::rest,[]⟩) :
    (∃ next, tableFill ⟨s,ambient,{f with code := .TABLE_FILL (.mk_uN index)::after}::rest,[]⟩ f rest index after = .next next ∧
      CoreTyped next ∧ Extend_store s next.store ∧
      NextSim ⟨s,ambient,{f with code := .TABLE_FILL (.mk_uN index)::after}::rest,[]⟩ next) ∨
    (tableFill ⟨s,ambient,{f with code := .TABLE_FILL (.mk_uN index)::after}::rest,[]⟩ f rest index after = .trap ∧
      ∃ count,0<count ∧ StepsHN count (decode ⟨s,ambient,{f with code := .TABLE_FILL (.mk_uN index)::after}::rest,[]⟩) []
        ⟨⟨s,ambient⟩,[.TRAP]⟩) := by
  have hf : FrameTyped s {f with code := .TABLE_FILL (.mk_uN index)::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | table_fill _ _ type limits bound selected contextWf instructionWf =>
    have lookup : C.TABLES[index]? = some (.mk_tabletype limits type) := by
      simp only [labelContext,proj_uN_0] at bound selected
      simpa only [getElem!_pos C.TABLES index bound,List.getElem?_eq_getElem bound] using congrArg some selected
    obtain ⟨address,object,mapped,found,objectType⟩ := table_lookup bindings lookup
    cases operandTypes with
    | cons destinationTyped tail => cases tail with
      | cons valueTyped tail => cases tail with
        | cons countTyped tail =>
          cases tail
          obtain ⟨destination,rfl,destinationBound⟩ := integer_val_inv (ty:=.I32) destinationTyped
          obtain ⟨reference,rfl,refTyped⟩ := reference_operand valueTyped
          obtain ⟨count,rfl,countBound⟩ := integer_val_inv (ty:=.I32) countTyped
          have destinationDecoded := integer_accepts .I32 destination destinationBound
          have countDecoded := integer_accepts .I32 count countBound
          simp only [numtype_Inn] at destinationDecoded countDecoded
          have rawTyped : Ref_ok s reference (tableElementType object.TYPE) := by rw [objectType]; exact refTyped
          obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf hf
          have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
          have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
          have indexBound : index<2^32 := by cases instructionWf; rename_i valid; cases valid; norm_num at *; omega
          have tableEq : fun_table ⟨s,f.toFrame⟩ (.mk_uN index) = object := by
            simp [fun_table,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
          by_cases inside : destination+count ≤ object.REFS.length
          · obtain ⟨extension,contents,functions⟩ := table_fill_preserves s f.toFrame index address destination object reference count
              typed.typed.store typed.contents mapped found rawTyped
            have frameNext : FrameTyped s {f with code:=after,vals:=front} [] := by
              simpa only [List.append_nil] using continuation [] .nil
            have fresh := (active_frame_preservation typed.typed frameNext rfl).extend_same extension functions
            apply Or.inl
            refine ⟨_,by simp only [tableFill,split,pop_three_append,mapped,destinationDecoded,as_reference_value,countDecoded,found,inside,ite_true,advance],
              ⟨fresh,contents⟩,extension,?_⟩
            have addressBound : f.module.TABLES[index]! < s.TABLES.length := by
              simp only [List.getElem!_eq_getElem?_getD,mapped,Option.getD_some]
              exact (List.getElem?_eq_some_iff.mp found).1
            have source := Segment.table_fill_steps s f.toFrame destination count index reference typed.typed.store frameWf
              destinationBound countBound indexBound (List.getElem?_eq_some_iff.mp mapped).1 addressBound
              (by rw [tableEq]; exact table_size_bound typed.contents (List.mem_of_getElem? found)) (by simpa only [tableEq] using inside)
            have full := bulk_empty_simulation s (Segment.tableFill s f.toFrame index destination reference count) ambient f rest
              (.TABLE_FILL (.mk_uN index)) after front [integerVal .I32 destination,val_ref reference,integerVal .I32 count]
              typed.typed.ambient labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.fillOperands,reference_admin_value,admininstr_instr,show admininstr_val (integerVal .I32 destination) = Segment.i32 destination from rfl,show admininstr_val (integerVal .I32 count) = Segment.i32 count from rfl] using source)
            simpa only [split] using full
          · apply Or.inr
            refine ⟨by simp only [tableFill,split,pop_three_append,mapped,destinationDecoded,as_reference_value,countDecoded,found,inside,ite_false],?_⟩
            have source := Segment.table_fill_trap s f.toFrame destination count index reference typed.typed.store frameWf
              destinationBound countBound indexBound (by simpa only [tableEq] using Nat.lt_of_not_ge inside)
            have full := operand_trap_simulation s ambient f rest (.TABLE_FILL (.mk_uN index)) after front
              [integerVal .I32 destination,val_ref reference,integerVal .I32 count] typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.fillOperands,reference_admin_value,admininstr_instr,show admininstr_val (integerVal .I32 destination) = Segment.i32 destination from rfl,show admininstr_val (integerVal .I32 count) = Segment.i32 count from rfl] using source)
            simpa only [split] using full
end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## TableSet -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

def tableSet (s : AState) (f : AFrame) (rest : List AFrame) (index : Nat) (after : List instr) : AResult :=
  match pop f.vals, f.module.TABLES[index]? with
  | some (prefixValues,value), some address => match pop prefixValues, asReference value, s.store.TABLES[address]? with
    | some (front,offset), some reference, some object => match integer .I32 offset with
      | some position =>
        if position < object.REFS.length then
          advance {s with store := Segment.tableWrite s.store f.toFrame index position reference}
            {f with code := after, vals := front} rest
        else .trap
      | none => .stuck
    | _,_,_ => .stuck
  | _,_ => .stuck

theorem table_set_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .TABLE_SET (.mk_uN index) :: after} :: rest,[]⟩) :
    (∃ next, tableSet ⟨s,ambient,{f with code := .TABLE_SET (.mk_uN index) :: after} :: rest,[]⟩ f rest index after = .next next ∧
      CoreTyped next ∧ Extend_store s next.store ∧
      NextSim ⟨s,ambient,{f with code := .TABLE_SET (.mk_uN index) :: after} :: rest,[]⟩ next) ∨
    (tableSet ⟨s,ambient,{f with code := .TABLE_SET (.mk_uN index) :: after} :: rest,[]⟩ f rest index after = .trap ∧
      ∃ count, 0 < count ∧ StepsHN count (decode ⟨s,ambient,{f with code := .TABLE_SET (.mk_uN index) :: after} :: rest,[]⟩) []
        ⟨⟨s,ambient⟩,[.TRAP]⟩) := by
  have hf : FrameTyped s {f with code := .TABLE_SET (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | table_set _ _ type limits bound selected contextWf instructionWf =>
    have lookup : C.TABLES[index]? = some (.mk_tabletype limits type) := by
      simp only [labelContext,proj_uN_0] at bound selected
      simpa only [getElem!_pos C.TABLES index bound,List.getElem?_eq_getElem bound] using congrArg some selected
    obtain ⟨address,object,mapped,found,objectType⟩ := table_lookup bindings lookup
    cases operandTypes with
    | cons offsetTyped tail =>
      cases tail with
      | cons valueTyped tail =>
        cases tail
        obtain ⟨position,rfl,positionBound⟩ := integer_val_inv (ty := .I32) offsetTyped
        obtain ⟨reference,rfl,refTyped⟩ := reference_operand valueTyped
        have decoded : integer .I32 (integerVal .I32 position) = some position := integer_accepts .I32 position positionBound
        have rawTyped : Ref_ok s reference (tableElementType object.TYPE) := by rw [objectType]; exact refTyped
        have split' : f.vals = (front ++ [integerVal .I32 position]) ++ [val_ref reference] := by simpa only [List.append_assoc,List.singleton_append] using split
        obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf hf
        have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
        have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
        have indexBound : index < 2^32 := by cases instructionWf; rename_i valid; cases valid; norm_num at *; omega
        have tableEq : fun_table ⟨s,f.toFrame⟩ (.mk_uN index) = object := by
          simp [fun_table,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
        by_cases inside : position < object.REFS.length
        · have extension := table_write_extends s f.toFrame index address position object reference typed.typed.store typed.contents mapped found
          have contents := table_write_contents s f.toFrame index address position object reference typed.typed.store typed.contents mapped found rawTyped
          have freshFrame := continuation [] .nil
          have actualFrame : FrameTyped s {f with code := after,vals := front} [] := by simpa only [List.append_nil] using freshFrame
          have fresh := (active_frame_preservation typed.typed actualFrame rfl).extend_same extension rfl
          apply Or.inl
          refine ⟨_,by simp only [tableSet,split',pop_append,mapped,as_reference_value,decoded,found,inside,ite_true,advance],
            ⟨fresh,contents⟩,extension,NextSim.single ?_⟩
          have source := Segment.table_write_step s f.toFrame index position reference typed.typed.store frameWf positionBound indexBound
            (List.getElem?_eq_some_iff.mp mapped).1 (by simpa only [tableEq] using inside)
          have full := mutable_stack_simulation s (Segment.tableWrite s f.toFrame index position reference) ambient f rest
            (.TABLE_SET (.mk_uN index)) after front [integerVal .I32 position,val_ref reference] []
            typed.typed.ambient labelsWf frontWf tailWf restWf heights
            (by simpa [vals,reference_admin_value,admininstr_instr,show admininstr_val (integerVal .I32 position) = Segment.i32 position from rfl] using source)
          simpa only [split,List.append_nil] using full
        · apply Or.inr
          refine ⟨by simp only [tableSet,split',pop_append,mapped,as_reference_value,decoded,found,inside,ite_false],?_⟩
          have source := table_set_trap_step s f.toFrame index position reference typed.typed.store frameWf indexBound positionBound
            (by simpa only [tableEq] using Nat.le_of_not_gt inside)
          have full := operand_trap_simulation s ambient f rest (.TABLE_SET (.mk_uN index)) after front
            [integerVal .I32 position,val_ref reference] typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
            (by simpa [vals,reference_admin_value,admininstr_instr,show admininstr_val (integerVal .I32 position) = Segment.i32 position from rfl] using source)
          simpa only [split] using full
end Itasca.Runtime.SourceMachine.Stateful

end
