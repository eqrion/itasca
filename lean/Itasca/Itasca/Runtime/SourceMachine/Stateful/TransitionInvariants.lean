import Itasca.Runtime.SourceMachine.Simulation
import Itasca.Runtime.SourceMachine.OwnershipExtension
import Itasca.Runtime.Spec.PrimitiveOperations
import Itasca.Runtime.SourceMachine.Stateful.AccessAndGrowth
import Itasca.Runtime.SourceMachine.Core.OperationsAndMemoryTyping
import Itasca.Runtime.SourceMachine.Sim.Control
import Itasca.Runtime.SourceMachine.Sim.Structured
import Itasca.Runtime.Spec.BulkOperations
import Itasca.Runtime.SourceMachine.StructureAndTyping
import Itasca.Runtime.SourceMachine.Stateful.Signature
import Itasca.Runtime.SourceMachine.Bound

open WebAssembly

/-!
Proofs for Runtime / SourceMachine / Stateful.

This module collects Mutation, TransitionInvariants.
Each section documents its contracts and consumers.
-/

/-! ## Mutation -/

section

/-!
# Stateful source-store mutation

Drop, bulk-memory and table updates retain source object ownership and stack operands.
Store replacement and fill/copy/init facts compose those mutations into flat source-
machine steps.
-/

/-! ## OwnershipStore -/

section

namespace Itasca.SourceMachine.Ownership
open WebAssembly Itasca.Spec Stateful

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

end Itasca.SourceMachine.Ownership

end

/-! ## Drops -/

section

/-!
Source data/element segment drops: store effects and typed continuation simulation.
-/

/-! ## Drop Store -/

section

namespace Itasca.SourceMachine.Stateful
open WebAssembly Itasca.Spec

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
end Itasca.SourceMachine.Stateful

end

/-! ## Drops -/

section

namespace Itasca.SourceMachine.Stateful
open WebAssembly Itasca.Spec

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

end Itasca.SourceMachine.Stateful

end

end

/-! ## BulkSimulation -/

section

namespace Itasca.SourceMachine.Stateful
open WebAssembly Itasca.Spec

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
end Itasca.SourceMachine.Stateful

end

/-! ## TableMutation -/

section

namespace Itasca.SourceMachine.Stateful
open WebAssembly Itasca.Spec

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
end Itasca.SourceMachine.Stateful

end

/-! ## FillStore -/

section

namespace Itasca.SourceMachine.Stateful
open WebAssembly Itasca.Spec

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
end Itasca.SourceMachine.Stateful

end

/-! ## Operands -/

section

namespace Itasca.SourceMachine.Stateful

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
end Itasca.SourceMachine.Stateful

end

/-! ## MemoryFill -/

section

namespace Itasca.SourceMachine.Stateful
open WebAssembly Itasca.Spec

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
end Itasca.SourceMachine.Stateful

end

/-! ## MemoryTransfer -/

section

/-!
Source memory copy and initialization, retaining their distinct segment/snapshot premises while sharing bounded transfer simulation.
-/

/-! ## Memory Copy -/

section

namespace Itasca.SourceMachine.Stateful
open WebAssembly Itasca.Spec

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
end Itasca.SourceMachine.Stateful

end

/-! ## Memory Init -/

section

namespace Itasca.SourceMachine.Stateful
open WebAssembly Itasca.Spec

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
end Itasca.SourceMachine.Stateful

end

end

/-! ## TableFill -/

section

namespace Itasca.SourceMachine.Stateful
open WebAssembly Itasca.Spec

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
end Itasca.SourceMachine.Stateful

end

/-! ## TableSet -/

section

namespace Itasca.SourceMachine.Stateful
open WebAssembly Itasca.Spec

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
end Itasca.SourceMachine.Stateful

end

end

/-! ## TransitionInvariants -/

section

/-!
# Transition Invariants

Stateful table, memory and segment transitions preserve their bounds and typing invariants.
-/

/-! ## TableTransfer -/

section

/-!
Source table copy and initialization, retaining reference and segment bounds in the common transfer argument.
-/

/-! ## Table Copy -/

section

namespace Itasca.SourceMachine.Stateful
open WebAssembly Itasca.Spec

def tableCopy (s : AState) (f : AFrame) (rest : List AFrame) (index sourceIndex : Nat) (after : List instr) : AResult :=
  match popThree f.vals, f.module.TABLES[index]?, f.module.TABLES[sourceIndex]? with
  | some (front,offset,value,size), some address, some sourceAddress =>
    match integer .I32 offset, integer .I32 value, integer .I32 size, s.store.TABLES[address]?, s.store.TABLES[sourceAddress]? with
    | some destination, some sourceOffset, some count, some object, some sourceObject =>
      if sourceOffset+count ≤ sourceObject.REFS.length ∧ destination+count ≤ object.REFS.length then
        advance {s with store := Segment.tableCopy s.store f.toFrame index sourceIndex destination sourceOffset count}
          {f with code := after,vals := front} rest
      else .trap
    | _,_,_,_,_ => .stuck
  | _,_,_ => .stuck

theorem table_copy_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index sourceIndex : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .TABLE_COPY (.mk_uN index) (.mk_uN sourceIndex)::after}::rest,[]⟩) :
    (∃ next, tableCopy ⟨s,ambient,{f with code := .TABLE_COPY (.mk_uN index) (.mk_uN sourceIndex)::after}::rest,[]⟩ f rest index sourceIndex after = .next next ∧
      CoreTyped next ∧ Extend_store s next.store ∧
      NextSim ⟨s,ambient,{f with code := .TABLE_COPY (.mk_uN index) (.mk_uN sourceIndex)::after}::rest,[]⟩ next) ∨
    (tableCopy ⟨s,ambient,{f with code := .TABLE_COPY (.mk_uN index) (.mk_uN sourceIndex)::after}::rest,[]⟩ f rest index sourceIndex after = .trap ∧
      ∃ count,0<count ∧ StepsHN count (decode ⟨s,ambient,{f with code := .TABLE_COPY (.mk_uN index) (.mk_uN sourceIndex)::after}::rest,[]⟩) []
        ⟨⟨s,ambient⟩,[.TRAP]⟩) := by
  have hf : FrameTyped s {f with code := .TABLE_COPY (.mk_uN index) (.mk_uN sourceIndex)::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | table_copy _ _ _ limits type sourceLimits bound selected sourceBound sourceSelected contextWf instructionWf =>
    have lookup : C.TABLES[index]? = some (.mk_tabletype limits type) := by
      simp only [labelContext,proj_uN_0] at bound selected
      simpa only [getElem!_pos C.TABLES index bound,List.getElem?_eq_getElem bound] using congrArg some selected
    obtain ⟨address,object,mapped,found,objectType⟩ := table_lookup bindings lookup
    have sourceLookup : C.TABLES[sourceIndex]? = some (.mk_tabletype sourceLimits type) := by
      simp only [labelContext,proj_uN_0] at sourceBound sourceSelected
      simpa only [getElem!_pos C.TABLES sourceIndex sourceBound,List.getElem?_eq_getElem sourceBound] using congrArg some sourceSelected
    obtain ⟨sourceAddress,sourceObject,sourceMapped,sourceFound,sourceType⟩ := table_lookup bindings sourceLookup
    have sameType : tableElementType object.TYPE = tableElementType sourceObject.TYPE := objectType.trans sourceType.symm
    cases operandTypes with
    | cons destinationTyped tail => cases tail with
      | cons valueTyped tail => cases tail with
        | cons countTyped tail =>
          cases tail
          obtain ⟨destination,rfl,destinationBound⟩ := integer_val_inv (ty:=.I32) destinationTyped
          obtain ⟨sourceOffset,rfl,sourceOffsetBound⟩ := integer_val_inv (ty:=.I32) valueTyped
          obtain ⟨count,rfl,countBound⟩ := integer_val_inv (ty:=.I32) countTyped
          have destinationDecoded := integer_accepts .I32 destination destinationBound
          have countDecoded := integer_accepts .I32 count countBound
          simp only [numtype_Inn] at destinationDecoded countDecoded
          have sourceDecoded : integer .I32 (integerVal .I32 sourceOffset) = some sourceOffset := integer_accepts .I32 sourceOffset sourceOffsetBound
          obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf hf
          have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
          have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
          have indexBound : index<2^32 := by cases instructionWf; rename_i valid _; cases valid; norm_num at *; omega
          have sourceIndexBound : sourceIndex<2^32 := by cases instructionWf; rename_i _ valid; cases valid; norm_num at *; omega
          have tableEq : fun_table ⟨s,f.toFrame⟩ (.mk_uN index) = object := by
            simp [fun_table,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
          have sourceEq : fun_table ⟨s,f.toFrame⟩ (.mk_uN sourceIndex) = sourceObject := by
            simp [fun_table,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,sourceMapped,sourceFound]
          by_cases inside : sourceOffset+count ≤ sourceObject.REFS.length ∧ destination+count ≤ object.REFS.length
          · obtain ⟨extension,contents⟩ := table_copy_preserves s f.toFrame index sourceIndex address sourceAddress destination sourceOffset count object sourceObject
              typed.typed.store typed.contents mapped sourceMapped found sourceFound sameType inside
            have frameNext : FrameTyped s {f with code:=after,vals:=front} [] := by
              simpa only [List.append_nil] using continuation [] .nil
            have fresh := (active_frame_preservation typed.typed frameNext rfl).extend_same extension rfl
            apply Or.inl
            refine ⟨_,by simp only [tableCopy,split,pop_three_append,mapped,sourceMapped,destinationDecoded,sourceDecoded,countDecoded,found,sourceFound,inside,and_true,ite_true,advance],
              ⟨fresh,contents⟩,extension,?_⟩
            have addressBound : f.module.TABLES[index]! < s.TABLES.length := by
              simp only [List.getElem!_eq_getElem?_getD,mapped,Option.getD_some]
              exact (List.getElem?_eq_some_iff.mp found).1
            have sourceAddressBound : f.module.TABLES[sourceIndex]! < s.TABLES.length := by
              simpa only [List.getElem!_eq_getElem?_getD,sourceMapped,Option.getD_some] using (List.getElem?_eq_some_iff.mp sourceFound).1
            have source := Segment.table_copy_steps s f.toFrame destination sourceOffset count index sourceIndex typed.typed.store frameWf
              destinationBound sourceOffsetBound countBound indexBound sourceIndexBound (List.getElem?_eq_some_iff.mp mapped).1 addressBound sourceAddressBound
              (by rw [tableEq,sourceEq]; exact ⟨table_size_bound typed.contents (List.mem_of_getElem? found),table_size_bound typed.contents (List.mem_of_getElem? sourceFound)⟩)
              (by simpa only [tableEq,sourceEq] using inside)
            have full := bulk_empty_simulation s (Segment.tableCopy s f.toFrame index sourceIndex destination sourceOffset count) ambient f rest
              (.TABLE_COPY (.mk_uN index) (.mk_uN sourceIndex)) after front [integerVal .I32 destination,integerVal .I32 sourceOffset,integerVal .I32 count]
              typed.typed.ambient labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.operands,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
            simpa only [split] using full
          · apply Or.inr
            refine ⟨by simp only [tableCopy,split,pop_three_append,mapped,sourceMapped,destinationDecoded,sourceDecoded,countDecoded,found,sourceFound,inside,ite_false],?_⟩
            have source := Segment.table_copy_trap s f.toFrame destination sourceOffset count index sourceIndex typed.typed.store frameWf
              destinationBound sourceOffsetBound countBound indexBound sourceIndexBound (by rw [tableEq,sourceEq]; omega)
            have full := operand_trap_simulation s ambient f rest (.TABLE_COPY (.mk_uN index) (.mk_uN sourceIndex)) after front
              [integerVal .I32 destination,integerVal .I32 sourceOffset,integerVal .I32 count] typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.operands,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
            simpa only [split] using full
end Itasca.SourceMachine.Stateful

end

/-! ## Table Init -/

section

namespace Itasca.SourceMachine.Stateful
open WebAssembly Itasca.Spec

def tableInit (s : AState) (f : AFrame) (rest : List AFrame) (index sourceIndex : Nat) (after : List instr) : AResult :=
  match popThree f.vals, f.module.TABLES[index]?, f.module.ELEMS[sourceIndex]? with
  | some (front,offset,value,size), some address, some sourceAddress =>
    match integer .I32 offset, integer .I32 value, integer .I32 size, s.store.TABLES[address]?, s.store.ELEMS[sourceAddress]? with
    | some destination, some sourceOffset, some count, some object, some sourceObject =>
      if sourceOffset+count ≤ sourceObject.REFS.length ∧ destination+count ≤ object.REFS.length then
        advance {s with store := Segment.tableInit s.store f.toFrame index sourceIndex destination sourceOffset count}
          {f with code := after,vals := front} rest
      else .trap
    | _,_,_,_,_ => .stuck
  | _,_,_ => .stuck

theorem table_init_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index sourceIndex : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .TABLE_INIT (.mk_uN index) (.mk_uN sourceIndex)::after}::rest,[]⟩) :
    (∃ next, tableInit ⟨s,ambient,{f with code := .TABLE_INIT (.mk_uN index) (.mk_uN sourceIndex)::after}::rest,[]⟩ f rest index sourceIndex after = .next next ∧
      CoreTyped next ∧ Extend_store s next.store ∧
      NextSim ⟨s,ambient,{f with code := .TABLE_INIT (.mk_uN index) (.mk_uN sourceIndex)::after}::rest,[]⟩ next) ∨
    (tableInit ⟨s,ambient,{f with code := .TABLE_INIT (.mk_uN index) (.mk_uN sourceIndex)::after}::rest,[]⟩ f rest index sourceIndex after = .trap ∧
      ∃ count,0<count ∧ StepsHN count (decode ⟨s,ambient,{f with code := .TABLE_INIT (.mk_uN index) (.mk_uN sourceIndex)::after}::rest,[]⟩) []
        ⟨⟨s,ambient⟩,[.TRAP]⟩) := by
  have hf : FrameTyped s {f with code := .TABLE_INIT (.mk_uN index) (.mk_uN sourceIndex)::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | table_init _ _ _ limits type bound selected sourceBound sourceSelected contextWf instructionWf =>
    have lookup : C.TABLES[index]? = some (.mk_tabletype limits type) := by
      simp only [labelContext,proj_uN_0] at bound selected
      simpa only [getElem!_pos C.TABLES index bound,List.getElem?_eq_getElem bound] using congrArg some selected
    obtain ⟨address,object,mapped,found,objectType⟩ := table_lookup bindings lookup
    simp only [labelContext,proj_uN_0] at sourceBound sourceSelected
    have sourceLeft : sourceIndex < f.module.ELEMS.length := by rw [bindings.elems.length_eq]; exact sourceBound
    obtain ⟨sourceObject,sourceFound,sourceTyped⟩ := bindings.elems.get sourceLeft sourceBound
    simp only [List.get_eq_getElem] at sourceFound sourceTyped
    have sourceMapped : f.module.ELEMS[sourceIndex]? = some f.module.ELEMS[sourceIndex] := List.getElem?_eq_getElem sourceLeft
    obtain ⟨sourceType,elementBound,elementRefs⟩ := element_refs_typed sourceTyped
    have sourceType' : sourceObject.TYPE = type := by
      rw [sourceType]
      simpa only [labelContext,proj_uN_0,getElem!_pos C.ELEMS sourceIndex sourceBound] using sourceSelected
    have sameType : tableElementType object.TYPE = sourceObject.TYPE := objectType.trans sourceType'.symm
    cases operandTypes with
    | cons destinationTyped tail => cases tail with
      | cons valueTyped tail => cases tail with
        | cons countTyped tail =>
          cases tail
          obtain ⟨destination,rfl,destinationBound⟩ := integer_val_inv (ty:=.I32) destinationTyped
          obtain ⟨sourceOffset,rfl,sourceOffsetBound⟩ := integer_val_inv (ty:=.I32) valueTyped
          obtain ⟨count,rfl,countBound⟩ := integer_val_inv (ty:=.I32) countTyped
          have destinationDecoded := integer_accepts .I32 destination destinationBound
          have countDecoded := integer_accepts .I32 count countBound
          simp only [numtype_Inn] at destinationDecoded countDecoded
          have sourceDecoded : integer .I32 (integerVal .I32 sourceOffset) = some sourceOffset := integer_accepts .I32 sourceOffset sourceOffsetBound
          obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf hf
          have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
          have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
          have indexBound : index<2^32 := by cases instructionWf; rename_i valid _; cases valid; norm_num at *; omega
          have sourceIndexBound : sourceIndex<2^32 := by cases instructionWf; rename_i _ valid; cases valid; norm_num at *; omega
          have tableEq : fun_table ⟨s,f.toFrame⟩ (.mk_uN index) = object := by
            simp [fun_table,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
          have sourceEq : fun_elem ⟨s,f.toFrame⟩ (.mk_uN sourceIndex) = sourceObject := by
            simp [fun_elem,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,sourceMapped,sourceFound]
          by_cases inside : sourceOffset+count ≤ sourceObject.REFS.length ∧ destination+count ≤ object.REFS.length
          · obtain ⟨extension,contents,functions⟩ := table_init_preserves s f.toFrame index sourceIndex address f.module.ELEMS[sourceIndex] destination sourceOffset count object sourceObject
              typed.typed.store typed.contents mapped found sourceMapped sourceFound sameType inside
            have frameNext : FrameTyped s {f with code:=after,vals:=front} [] := by
              simpa only [List.append_nil] using continuation [] .nil
            have fresh := (active_frame_preservation typed.typed frameNext rfl).extend_same extension functions
            apply Or.inl
            refine ⟨_,by simp only [tableInit,split,pop_three_append,mapped,sourceMapped,destinationDecoded,sourceDecoded,countDecoded,found,sourceFound,inside,and_true,ite_true,advance],
              ⟨fresh,contents⟩,extension,?_⟩
            have addressBound : f.module.TABLES[index]! < s.TABLES.length := by
              simp only [List.getElem!_eq_getElem?_getD,mapped,Option.getD_some]
              exact (List.getElem?_eq_some_iff.mp found).1
            have source := Segment.table_init_steps s f.toFrame destination sourceOffset count index sourceIndex typed.typed.store frameWf
              destinationBound sourceOffsetBound countBound indexBound sourceIndexBound (List.getElem?_eq_some_iff.mp mapped).1 addressBound
              (by rw [tableEq]; exact table_size_bound typed.contents (List.mem_of_getElem? found))
              (by rw [sourceEq]; exact elementBound) (by simpa only [tableEq,sourceEq] using inside)
            have full := bulk_empty_simulation s (Segment.tableInit s f.toFrame index sourceIndex destination sourceOffset count) ambient f rest
              (.TABLE_INIT (.mk_uN index) (.mk_uN sourceIndex)) after front [integerVal .I32 destination,integerVal .I32 sourceOffset,integerVal .I32 count]
              typed.typed.ambient labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.operands,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
            simpa only [split] using full
          · apply Or.inr
            refine ⟨by simp only [tableInit,split,pop_three_append,mapped,sourceMapped,destinationDecoded,sourceDecoded,countDecoded,found,sourceFound,inside,ite_false],?_⟩
            have source := Segment.table_init_trap s f.toFrame destination sourceOffset count index sourceIndex typed.typed.store frameWf
              destinationBound sourceOffsetBound countBound indexBound sourceIndexBound (by rw [tableEq,sourceEq]; omega)
            have full := operand_trap_simulation s ambient f rest (.TABLE_INIT (.mk_uN index) (.mk_uN sourceIndex)) after front
              [integerVal .I32 destination,integerVal .I32 sourceOffset,integerVal .I32 count] typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
              (by simpa [vals,Segment.operands,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
            simpa only [split] using full
end Itasca.SourceMachine.Stateful

end

end

/-! ## Transition -/

section

namespace Itasca.SourceMachine.Stateful
open WebAssembly Itasca.Spec

/-- The only nondeterministic choices are successful growth or permitted refusal. -/
structure Selection where
  memory : Option meminst := none
  table : Option tableinst := none

/-- Growth choices refer to the actual operands and selected source object. -/
def Selection.Allowed (choice : Selection) (op : Instruction) (s : store) (f : AFrame) : Prop :=
  match op with
  | .memoryGrow => ∀ front delta address object,
      f.vals = front ++ [integerVal .I32 delta] → f.module.MEMS[0]? = some address →
      s.MEMS[address]? = some object → MemoryGrowthChoice object delta choice.memory
  | .tableGrow index => ∀ front reference delta address object,
      f.vals = front ++ [val_ref reference,integerVal .I32 delta] →
      f.module.TABLES[index]? = some address → s.TABLES[address]? = some object →
      TableGrowthChoice object delta reference choice.table
  | _ => True

theorem Selection.refusal_allowed (op : Instruction) (s : store) (f : AFrame) :
    Selection.Allowed {} op s f := by
  cases op <;> simp only [Selection.Allowed]
  all_goals first | trivial | intros; constructor

def evaluate (choice : Selection) (op : Instruction) (s : AState) (f : AFrame)
    (rest : List AFrame) (after : List instr) : AResult :=
  match op with
  | .refNull type => refNull s f rest type after
  | .refFunc index => refFunc s f rest index after
  | .refIsNull => refIsNull s f rest after
  | .tableGet index => tableGet s f rest index after
  | .tableSet index => tableSet s f rest index after
  | .tableSize index => tableSize s f rest index after
  | .tableGrow index => tableGrow choice.table s f rest index after
  | .tableFill index => tableFill s f rest index after
  | .tableCopy index source => tableCopy s f rest index source after
  | .tableInit index source => tableInit s f rest index source after
  | .elemDrop index => elementDrop s f rest index after
  | .memorySize => memorySize s f rest after
  | .memoryGrow => memoryGrow choice.memory s f rest after
  | .memoryFill => memoryFill s f rest after
  | .memoryCopy => memoryCopy s f rest after
  | .memoryInit index => memoryInit s f rest index after
  | .dataDrop index => dataDrop s f rest index after

/-- This relation selects a runtime result without choosing successful allocation in advance. -/
def Transition (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr)
    (op : Instruction) (result : AResult) : Prop :=
  ∃ choice, choice.Allowed op s.store f ∧ evaluate choice op s f rest after = result

def ResultSafe (initial : AState) : AResult → Prop
  | .next next => CoreTyped next ∧ Extend_store initial.store next.store ∧ NextSim initial next
  | .trap => ∃ count, 0 < count ∧ StepsHN count (decode initial) [] ⟨⟨initial.store,initial.ambient⟩,[.TRAP]⟩
  | _ => False

def Instruction.readOnly : Instruction → Bool
  | .refNull _ | .refFunc _ | .refIsNull | .tableGet _ | .tableSize _ | .memorySize => true
  | _ => false

theorem evaluate_read_store (choice : Selection) (op : Instruction) (s : AState) (f : AFrame)
    (rest : List AFrame) (after : List instr) (next : AState) (readOnly : op.readOnly = true)
    (result : evaluate choice op s f rest after = .next next) : next.store = s.store := by
  cases op <;> simp only [Instruction.readOnly, Bool.false_eq_true] at readOnly
  all_goals simp only [evaluate,refNull,refFunc,refIsNull,tableGet,tableSize,memorySize,advance] at result
  all_goals repeat first | split at result | (cases result; rfl) | contradiction

theorem evaluate_safe (choice : Selection) (op : Instruction) (s : store) (ambient : frame)
    (f : AFrame) (rest : List AFrame) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (allowed : choice.Allowed op s f) :
    ResultSafe ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩
      (evaluate choice op ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ f rest after) := by
  cases op with
  | refNull type =>
    obtain ⟨next,result,fresh,simulation⟩ := ref_null_progress s ambient f rest type after typed
    have same := evaluate_read_store choice (.refNull type) ⟨s,ambient,{f with code := (.refNull type : Instruction).source::after}::rest,[]⟩ f rest after next rfl result
    change ResultSafe _ (refNull _ f rest type after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh, by rw [same]; exact extend_store_refl _ typed.typed.store, simulation⟩
  | refFunc index =>
    obtain ⟨next,result,fresh,simulation⟩ := ref_func_progress s ambient f rest index after typed
    have same := evaluate_read_store choice (.refFunc index) ⟨s,ambient,{f with code := (.refFunc index : Instruction).source::after}::rest,[]⟩ f rest after next rfl result
    change ResultSafe _ (refFunc _ f rest index after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh, by rw [same]; exact extend_store_refl _ typed.typed.store, simulation⟩
  | refIsNull =>
    obtain ⟨next,result,fresh,simulation⟩ := ref_is_null_progress s ambient f rest after typed
    have same := evaluate_read_store choice (.refIsNull) ⟨s,ambient,{f with code := (.refIsNull : Instruction).source::after}::rest,[]⟩ f rest after next rfl result
    change ResultSafe _ (refIsNull _ f rest after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh, by rw [same]; exact extend_store_refl _ typed.typed.store, simulation⟩
  | tableSize index =>
    obtain ⟨next,result,fresh,simulation⟩ := table_size_progress s ambient f rest index after typed
    have same := evaluate_read_store choice (.tableSize index) ⟨s,ambient,{f with code := (.tableSize index : Instruction).source::after}::rest,[]⟩ f rest after next rfl result
    change ResultSafe _ (tableSize _ f rest index after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh, by rw [same]; exact extend_store_refl _ typed.typed.store, simulation⟩
  | memorySize =>
    obtain ⟨next,result,fresh,simulation⟩ := memory_size_progress s ambient f rest after typed
    have same := evaluate_read_store choice (.memorySize) ⟨s,ambient,{f with code := (.memorySize : Instruction).source::after}::rest,[]⟩ f rest after next rfl result
    change ResultSafe _ (memorySize _ f rest after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh, by rw [same]; exact extend_store_refl _ typed.typed.store, simulation⟩
  | tableGet index =>
    rcases table_get_progress s ambient f rest index after typed with ⟨next,result,fresh,simulation⟩ | ⟨result,trap⟩
    · have same := evaluate_read_store choice (.tableGet index) ⟨s,ambient,{f with code := (.tableGet index : Instruction).source::after}::rest,[]⟩ f rest after next rfl result
      change ResultSafe _ (tableGet _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh, by rw [same]; exact extend_store_refl _ typed.typed.store, simulation⟩
    · change ResultSafe _ (tableGet _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | tableSet index =>
    rcases table_set_progress s ambient f rest index after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ResultSafe _ (tableSet _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ResultSafe _ (tableSet _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | tableFill index =>
    rcases table_fill_progress s ambient f rest index after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ResultSafe _ (tableFill _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ResultSafe _ (tableFill _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | tableCopy index source =>
    rcases table_copy_progress s ambient f rest index source after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ResultSafe _ (tableCopy _ f rest index source after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ResultSafe _ (tableCopy _ f rest index source after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | tableInit index source =>
    rcases table_init_progress s ambient f rest index source after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ResultSafe _ (tableInit _ f rest index source after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ResultSafe _ (tableInit _ f rest index source after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | memoryFill =>
    rcases memory_fill_progress s ambient f rest  after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ResultSafe _ (memoryFill _ f rest  after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ResultSafe _ (memoryFill _ f rest  after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | memoryCopy =>
    rcases memory_copy_progress s ambient f rest  after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ResultSafe _ (memoryCopy _ f rest  after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ResultSafe _ (memoryCopy _ f rest  after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | memoryInit index =>
    rcases memory_init_progress s ambient f rest index after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ResultSafe _ (memoryInit _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ResultSafe _ (memoryInit _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | elemDrop index =>
    obtain ⟨next,result,fresh,extended,simulation⟩ := element_drop_progress s ambient f rest index after typed
    change ResultSafe _ (elementDrop _ f rest index after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh,extended,simulation⟩
  | dataDrop index =>
    obtain ⟨next,result,fresh,extended,simulation⟩ := data_drop_progress s ambient f rest index after typed
    change ResultSafe _ (dataDrop _ f rest index after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh,extended,simulation⟩
  | memoryGrow =>
    obtain ⟨front,delta,address,object,values,mapped,found,choices⟩ := memory_grow_choices s ambient f rest after typed
    obtain ⟨next,result,fresh,extended,simulation⟩ := choices choice.memory (allowed front delta address object values mapped found)
    change ResultSafe _ (memoryGrow _ _ f rest after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh,extended,simulation⟩
  | tableGrow index =>
    obtain ⟨front,reference,delta,address,object,values,mapped,found,choices⟩ := table_grow_choices s ambient f rest index after typed
    obtain ⟨next,result,fresh,extended,simulation⟩ := choices choice.table (allowed front reference delta address object values mapped found)
    change ResultSafe _ (tableGrow _ _ f rest index after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh,extended,simulation⟩

theorem transition_safe (op : Instruction) (s : store) (ambient : frame)
    (f : AFrame) (rest : List AFrame) (after : List instr) (result : AResult)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (step : Transition ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ f rest after op result) :
    ResultSafe ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ result := by
  obtain ⟨choice,allowed,rfl⟩ := step
  exact evaluate_safe choice op s ambient f rest after typed allowed

theorem transition_next (op : Instruction) (s : store) (ambient : frame)
    (f : AFrame) (rest : List AFrame) (after : List instr) (next : AState)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (step : Transition ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ f rest after op (.next next)) :
    CoreTyped next ∧ Extend_store s next.store ∧
      NextSim ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ next :=
  transition_safe op s ambient f rest after (.next next) typed step

theorem transition_trap (op : Instruction) (s : store) (ambient : frame)
    (f : AFrame) (rest : List AFrame) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (step : Transition ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ f rest after op .trap) :
    ∃ count,0<count ∧ StepsHN count (decode ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩) []
      ⟨⟨s,ambient⟩,[.TRAP]⟩ :=
  transition_safe op s ambient f rest after .trap typed step

end Itasca.SourceMachine.Stateful

end

/-! ## Ownership -/

section

/-!
Stateful ownership preservation, composing primitive updates, bulk operations and growth under retained heap ownership.
-/

/-! ## Ownership Primitives -/

section

namespace Itasca.SourceMachine.Ownership
open WebAssembly Itasca.Spec Stateful

theorem stateful_owned_advance {bounds s f rest next}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : advance s f rest = .next next) : StatefulOwned bounds next :=
  ⟨ownership_advance results frame frames step,by cases step; exact heap⟩

theorem as_reference_owned {bounds value reference} (owned : ValueOwned bounds value)
    (decoded : asReference value = some reference) : ValueOwned bounds (val_ref reference) := by
  cases value <;> simp only [asReference] at decoded <;> cases decoded <;> exact owned

theorem stateful_ref_null_owned {bounds s f rest next type after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : refNull s f rest type after = .next next) : StatefulOwned bounds next := by
  apply stateful_owned_advance heap results _ frames step
  refine ⟨frame.1,values_owned_append.mpr ⟨frame.2,?_⟩⟩
  cases type <;> simp [ValuesOwned,ValueOwned]

theorem stateful_ref_func_owned {bounds s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (issued : ∀ address,f.module.FUNCS[index]? = some address → address < bounds.functions)
    (step : refFunc s f rest index after = .next next) : StatefulOwned bounds next := by
  unfold refFunc at step
  split at step
  · contradiction
  next address mapped =>
    apply stateful_owned_advance heap results _ frames step
    exact ⟨frame.1,values_owned_append.mpr ⟨frame.2,values_owned_cons.mpr ⟨issued address mapped,values_owned_nil _⟩⟩⟩

theorem stateful_ref_is_null_owned {bounds s f rest next after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : refIsNull s f rest after = .next next) : StatefulOwned bounds next := by
  unfold refIsNull at step
  split at step
  · contradiction
  next front value popped =>
    have prefixOwned := (frame.2.pop popped).1
    repeat' first | split at step | contradiction
    all_goals
      apply stateful_owned_advance heap results _ frames step
      exact ⟨frame.1,values_owned_append.mpr ⟨prefixOwned,by simp [ValuesOwned,ValueOwned,integerVal]⟩⟩

theorem stateful_table_get_owned {bounds s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : tableGet s f rest index after = .next next) : StatefulOwned bounds next := by
  unfold tableGet at step
  split at step
  next front value address popped mapped =>
    have prefixOwned := (frame.2.pop popped).1
    split at step
    next position object decoded found =>
      split at step
      next inside =>
        apply stateful_owned_advance heap results _ frames step
        refine ⟨frame.1,values_owned_append.mpr ⟨prefixOwned,values_owned_cons.mpr ⟨?_,values_owned_nil _⟩⟩⟩
        exact heap.tables object (List.mem_of_getElem? found) _ (List.getElem_mem inside)
      · contradiction
    · contradiction
  · contradiction

theorem stateful_table_set_owned {bounds s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : tableSet s f rest index after = .next next) : StatefulOwned bounds next := by
  unfold tableSet at step
  split at step
  next first value address popped mapped =>
    have firstOwned := frame.2.pop popped
    split at step
    next front offset reference object previous decoded found =>
      have prefixOwned := (firstOwned.1.pop previous).1
      have valueOwned := as_reference_owned firstOwned.2 decoded
      repeat' first | split at step | contradiction
      all_goals
        apply stateful_owned_advance (step := step)
        · exact heap.table_write _ _ _ _ valueOwned
        · exact results
        · exact ⟨frame.1,prefixOwned⟩
        · exact frames
    · contradiction
  · contradiction

theorem stateful_table_size_owned {bounds s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : tableSize s f rest index after = .next next) : StatefulOwned bounds next := by
  unfold tableSize at step
  repeat' first | split at step | contradiction
  all_goals
    apply stateful_owned_advance heap results _ frames step
    exact ⟨frame.1,values_owned_append.mpr ⟨frame.2,by simp [ValuesOwned,ValueOwned,integerVal]⟩⟩

theorem stateful_memory_size_owned {bounds s f rest next after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : memorySize s f rest after = .next next) : StatefulOwned bounds next := by
  unfold memorySize at step
  repeat' first | split at step | contradiction
  all_goals
    apply stateful_owned_advance heap results _ frames step
    exact ⟨frame.1,values_owned_append.mpr ⟨frame.2,by simp [ValuesOwned,ValueOwned,integerVal]⟩⟩

theorem stateful_element_drop_owned {bounds s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : elementDrop s f rest index after = .next next) : StatefulOwned bounds next := by
  unfold elementDrop at step
  repeat' first | split at step | contradiction
  all_goals
    apply stateful_owned_advance (step := step)
    · exact heap.elem_drop f.toFrame index
    · exact results
    · exact frame
    · exact frames

theorem stateful_data_drop_owned {bounds s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : dataDrop s f rest index after = .next next) : StatefulOwned bounds next := by
  unfold dataDrop at step
  repeat' first | split at step | contradiction
  all_goals
    apply stateful_owned_advance (step := step)
    · exact heap.data_drop f.toFrame index
    · exact results
    · exact frame
    · exact frames
end Itasca.SourceMachine.Ownership

end

/-! ## Ownership Bulk -/

section

namespace Itasca.SourceMachine.Ownership
open WebAssembly Itasca.Spec Stateful

theorem ValuesOwned.pop_three {bounds values front a b c} (owned : ValuesOwned bounds values)
    (popped : Stateful.popThree values = some (front,a,b,c)) :
    ValuesOwned bounds front ∧ ValueOwned bounds a ∧ ValueOwned bounds b ∧ ValueOwned bounds c := by
  unfold Stateful.popThree at popped
  split at popped
  · contradiction
  next first last one =>
    have h1 := owned.pop one
    split at popped
    · contradiction
    next second middle two =>
      have h2 := h1.1.pop two
      split at popped
      · contradiction
      next third start three =>
        have h3 := h2.1.pop three
        cases popped
        exact ⟨h3.1,h3.2,h2.2,h1.2⟩

theorem stateful_memory_fill_owned {bounds s f rest next after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : memoryFill s f rest after = .next next) : StatefulOwned bounds next := by
  unfold memoryFill at step
  split at step
  next front offset value size address popped mapped =>
    have prefixOwned := (frame.2.pop_three popped).1
    repeat' first | split at step | contradiction
    all_goals
      apply stateful_owned_advance (step := step)
      · exact heap.memory_fill _ _ _ _
      · exact results
      · exact ⟨frame.1,prefixOwned⟩
      · exact frames
  · contradiction

theorem stateful_memory_copy_owned {bounds s f rest next after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : memoryCopy s f rest after = .next next) : StatefulOwned bounds next := by
  unfold memoryCopy at step
  split at step
  next front offset value size address popped mapped =>
    have prefixOwned := (frame.2.pop_three popped).1
    repeat' first | split at step | contradiction
    all_goals
      apply stateful_owned_advance (step := step)
      · exact heap.memory_copy _ _ _ _
      · exact results
      · exact ⟨frame.1,prefixOwned⟩
      · exact frames
  · contradiction

theorem stateful_memory_init_owned {bounds s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : memoryInit s f rest index after = .next next) : StatefulOwned bounds next := by
  unfold memoryInit at step
  split at step
  next front offset value size address dataAddress popped mapped dataMapped =>
    have prefixOwned := (frame.2.pop_three popped).1
    repeat' first | split at step | contradiction
    all_goals
      apply stateful_owned_advance (step := step)
      · exact heap.memory_init _ _ _ _ _
      · exact results
      · exact ⟨frame.1,prefixOwned⟩
      · exact frames
  · contradiction

theorem stateful_table_fill_owned {bounds s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : tableFill s f rest index after = .next next) : StatefulOwned bounds next := by
  unfold tableFill at step
  split at step
  next front offset value size address popped mapped =>
    have input := frame.2.pop_three popped
    split at step
    next destination reference count object destinationEq referenceEq countEq found =>
      have valueOwned := as_reference_owned input.2.2.1 referenceEq
      split at step
      next inside =>
        apply stateful_owned_advance (step := step)
        · exact heap.table_fill _ _ _ _ _ valueOwned
        · exact results
        · exact ⟨frame.1,input.1⟩
        · exact frames
      · contradiction
    · contradiction
  · contradiction

theorem stateful_table_copy_owned {bounds s f rest next index sourceIndex after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : tableCopy s f rest index sourceIndex after = .next next) : StatefulOwned bounds next := by
  unfold tableCopy at step
  split at step
  next front offset value size address sourceAddress popped mapped sourceMapped =>
    have prefixOwned := (frame.2.pop_three popped).1
    split at step
    next destination source count object sourceObject destinationEq sourceEq countEq found sourceFound =>
      split at step
      next inside =>
        apply stateful_owned_advance (step := step)
        · exact heap.table_copy _ _ _ _ _ _ _ _ _ _ mapped sourceMapped found sourceFound inside
        · exact results
        · exact ⟨frame.1,prefixOwned⟩
        · exact frames
      · contradiction
    · contradiction
  · contradiction

theorem stateful_table_init_owned {bounds s f rest next index sourceIndex after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : tableInit s f rest index sourceIndex after = .next next) : StatefulOwned bounds next := by
  unfold tableInit at step
  split at step
  next front offset value size address sourceAddress popped mapped sourceMapped =>
    have prefixOwned := (frame.2.pop_three popped).1
    split at step
    next destination source count object sourceObject destinationEq sourceEq countEq found sourceFound =>
      split at step
      next inside =>
        apply stateful_owned_advance (step := step)
        · exact heap.table_init _ _ _ _ _ _ _ _ sourceMapped sourceFound inside.1
        · exact results
        · exact ⟨frame.1,prefixOwned⟩
        · exact frames
      · contradiction
    · contradiction
  · contradiction
end Itasca.SourceMachine.Ownership

end

/-! ## Ownership Growth -/

section

namespace Itasca.SourceMachine.Ownership
open WebAssembly Itasca.Spec Stateful

theorem stateful_memory_grow_owned {bounds choice s f rest next after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (step : memoryGrow choice s f rest after = .next next) : StatefulOwned bounds next := by
  unfold memoryGrow at step
  split at step
  next front value address popped mapped =>
    have prefixOwned := (frame.2.pop popped).1
    repeat' first | split at step | contradiction
    all_goals try simp_all only [Option.some.injEq,Prod.mk.injEq,as_reference_value]
    all_goals
      apply stateful_owned_advance (step := step)
      · exact heap.metadata rfl rfl rfl rfl
      · exact results
      · exact ⟨frame.1,values_owned_append.mpr ⟨prefixOwned,by simp [ValuesOwned,ValueOwned,integerVal]⟩⟩
      · exact frames
  · contradiction

theorem stateful_table_grow_owned {bounds choice s f rest next index after}
    (heap : StatefulHeapOwned bounds s.store) (results : ValuesOwned bounds s.results)
    (frame : FrameOwned bounds f) (frames : ∀ item ∈ rest,FrameOwned bounds item)
    (front : List val) (reference : ref) (delta address : Nat) (object : tableinst)
    (values : f.vals = front ++ [val_ref reference,integerVal .I32 delta])
    (mapped : f.module.TABLES[index]? = some address) (found : s.store.TABLES[address]? = some object)
    (allowed : TableGrowthChoice object delta reference choice)
    (step : tableGrow choice s f rest index after = .next next) : StatefulOwned bounds next := by
  have input : ValuesOwned bounds front ∧ ValueOwned bounds (val_ref reference) := by
    have owned := frame.2
    rw [values] at owned
    exact ⟨(values_owned_append.mp owned).1,(values_owned_cons.mp (values_owned_append.mp owned).2).1⟩
  have split : f.vals = (front ++ [val_ref reference]) ++ [integerVal .I32 delta] := by
    simpa [List.append_assoc] using values
  cases allowed with
  | refused =>
    simp only [tableGrow,split,pop_append,mapped,found,as_reference_value] at step
    repeat' first | split at step | contradiction
    all_goals try simp_all only [Option.some.injEq,Prod.mk.injEq,as_reference_value]
    all_goals
      apply stateful_owned_advance (step := step)
      · exact heap
      · exact results
      · exact ⟨frame.1,values_owned_append.mpr ⟨input.1,by simp [ValuesOwned,ValueOwned,integerVal]⟩⟩
      · exact frames
  | @grown fresh grown =>
    have newHeap := heap.table_grow address object fresh delta reference (List.mem_of_getElem? found) input.2 grown
    simp only [tableGrow,split,pop_append,mapped,found,as_reference_value] at step
    repeat' first | split at step | contradiction
    all_goals try simp_all only [Option.some.injEq,Prod.mk.injEq,as_reference_value]
    all_goals
      apply stateful_owned_advance (step := step)
      · exact newHeap
      · exact results
      · exact ⟨frame.1,values_owned_append.mpr ⟨input.1,by simp [ValuesOwned,ValueOwned,integerVal]⟩⟩
      · exact frames
end Itasca.SourceMachine.Ownership

end

/-! ## Ownership -/

section

namespace Itasca.SourceMachine.Ownership
open WebAssembly Itasca.Spec Stateful

theorem StatefulHeapOwned.frame_function {bounds s} {f : AFrame} {instruction : instr} {after : List instr}
    (heap : StatefulHeapOwned bounds s) (typed : FrameTyped s {f with code := instruction::after} [])
    (index address : Nat) (mapped : f.module.FUNCS[index]? = some address) : address < bounds.functions := by
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands typed
  have mappedBound := (List.getElem?_eq_some_iff.mp mapped).1
  have bound : index < C.FUNCS.length := by rw [←bindings.funcs.length_eq]; exact mappedBound
  obtain ⟨fn,found,_⟩ := bindings.funcs.get mappedBound bound
  simp only [List.get_eq_getElem] at found
  have addressEq : f.module.FUNCS[index] = address := (List.getElem?_eq_some_iff.mp mapped).2
  rw [addressEq] at found
  exact Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp found).1 heap.functions

theorem evaluate_owned (bounds : Bounds) (choice : Selection) (op : Instruction)
    (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame) (after : List instr) (next : AState)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (owned : StatefulOwned bounds ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (allowed : choice.Allowed op s f)
    (step : evaluate choice op ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ f rest after = .next next) :
    StatefulOwned bounds next := by
  have frame : FrameOwned bounds f := owned.values.2 {f with code := op.source::after} (List.mem_cons_self ..)
  have frames : ∀ item ∈ rest,FrameOwned bounds item := fun item member => owned.values.2 item (by simp [member])
  cases op with
  | refNull type =>
    exact stateful_ref_null_owned owned.heap owned.values.1 frame frames step
  | refIsNull =>
    exact stateful_ref_is_null_owned owned.heap owned.values.1 frame frames step
  | tableGet index =>
    exact stateful_table_get_owned owned.heap owned.values.1 frame frames step
  | tableSet index =>
    exact stateful_table_set_owned owned.heap owned.values.1 frame frames step
  | tableSize index =>
    exact stateful_table_size_owned owned.heap owned.values.1 frame frames step
  | tableFill index =>
    exact stateful_table_fill_owned owned.heap owned.values.1 frame frames step
  | tableCopy index source =>
    exact stateful_table_copy_owned owned.heap owned.values.1 frame frames step
  | tableInit index source =>
    exact stateful_table_init_owned owned.heap owned.values.1 frame frames step
  | elemDrop index =>
    exact stateful_element_drop_owned owned.heap owned.values.1 frame frames step
  | memorySize =>
    exact stateful_memory_size_owned owned.heap owned.values.1 frame frames step
  | memoryGrow =>
    exact stateful_memory_grow_owned owned.heap owned.values.1 frame frames step
  | memoryFill =>
    exact stateful_memory_fill_owned owned.heap owned.values.1 frame frames step
  | memoryCopy =>
    exact stateful_memory_copy_owned owned.heap owned.values.1 frame frames step
  | memoryInit index =>
    exact stateful_memory_init_owned owned.heap owned.values.1 frame frames step
  | dataDrop index =>
    exact stateful_data_drop_owned owned.heap owned.values.1 frame frames step
  | refFunc index =>
    apply stateful_ref_func_owned owned.heap owned.values.1 frame frames _ step
    intro address mapped
    have active : FrameTyped s {f with code := (.refFunc index : Instruction).source::after} [] := by
      cases typed.typed.frames with | cons head _ => exact head
    exact owned.heap.frame_function active index address mapped
  | tableGrow index =>
    obtain ⟨front,reference,delta,address,object,values,mapped,found,_⟩ := table_grow_choices s ambient f rest index after typed
    exact stateful_table_grow_owned owned.heap owned.values.1 frame frames front reference delta address object
      values mapped found (allowed front reference delta address object values mapped found) step

theorem stateful_transition_owned (bounds : Bounds) (op : Instruction)
    (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame) (after : List instr) (next : AState)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (owned : StatefulOwned bounds ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (step : Transition ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ f rest after op (.next next)) :
    StatefulOwned bounds next := by
  obtain ⟨choice,allowed,evaluated⟩ := step
  exact evaluate_owned bounds choice op s ambient f rest after next typed owned allowed evaluated
end Itasca.SourceMachine.Ownership

end

end

/-! ## Bound -/

section

/-!
Stateful transition metadata and code-bound preservation, consumed by cumulative execution.
-/

/-! ## Metadata -/

section

namespace Itasca.SourceMachine.Stateful
open WebAssembly Itasca.Spec

theorem evaluate_frame (choice : Selection) (op : Instruction) (s : AState) (f : AFrame)
    (rest : List AFrame) (after : List instr) (next : AState)
    (result : evaluate choice op s f rest after = .next next) :
    ∃ values, next.frames = {f with code := after, vals := values}::rest ∧
      next.ambient = s.ambient ∧ next.results = s.results := by
  cases op <;> simp only [evaluate,refNull,refFunc,refIsNull,tableGet,tableSet,tableSize,tableGrow,
    tableFill,tableCopy,tableInit,elementDrop,memorySize,memoryGrow,memoryFill,memoryCopy,memoryInit,dataDrop] at result
  all_goals repeat first | split at result | contradiction
  all_goals cases result <;> exact ⟨_,rfl,rfl,rfl⟩

theorem transition_frame (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr)
    (op : Instruction) (next : AState) (step : Transition s f rest after op (.next next)) :
    ∃ values, next.frames = {f with code := after,vals := values}::rest ∧
      next.ambient = s.ambient ∧ next.results = s.results := by
  obtain ⟨choice,_,result⟩ := step
  exact evaluate_frame choice op s f rest after next result
theorem table_fill_functions (s : store) (f : frame) (index destination : Nat) (value : ref) (count : Nat) :
    (Segment.tableFill s f index destination value count).FUNCS = s.FUNCS := by
  induction count generalizing s destination with
  | zero => rfl
  | succ count ih => exact ih (Segment.tableWrite s f index destination value) (destination+1)

theorem memory_fill_functions (s : store) (f : frame) (destination value count : Nat) :
    (Segment.memoryFill s f destination value count).FUNCS = s.FUNCS := by
  induction count generalizing s destination with
  | zero => rfl
  | succ count ih => exact ih (Segment.memoryWrite s f destination (Segment.fillByte value)) (Segment.next32 destination)

theorem memory_init_functions (s : store) (f : frame) (index destination source count : Nat) :
    (Segment.memoryInit s f index destination source count).FUNCS = s.FUNCS := by
  induction count generalizing s destination source with
  | zero => rfl
  | succ count ih => exact ih _ _ _

theorem table_init_functions (s : store) (f : frame) (index sourceIndex destination source count : Nat) :
    (Segment.tableInit s f index sourceIndex destination source count).FUNCS = s.FUNCS := by
  rw [Segment.table_init_eq]

theorem evaluate_functions (choice : Selection) (op : Instruction) (s : AState) (f : AFrame)
    (rest : List AFrame) (after : List instr) (next : AState)
    (result : evaluate choice op s f rest after = .next next) : next.store.FUNCS = s.store.FUNCS := by
  cases op <;> simp only [evaluate,refNull,refFunc,refIsNull,tableGet,tableSet,tableSize,tableGrow,
    tableFill,tableCopy,tableInit,elementDrop,memorySize,memoryGrow,memoryFill,memoryCopy,memoryInit,dataDrop,advance] at result
  all_goals repeat' first | split at result | contradiction
  all_goals cases result
  all_goals first | rfl | apply table_fill_functions | apply memory_fill_functions | apply table_init_functions | apply memory_init_functions

theorem transition_functions (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr)
    (op : Instruction) (next : AState) (step : Transition s f rest after op (.next next)) :
    next.store.FUNCS = s.store.FUNCS := by
  obtain ⟨choice,_,result⟩ := step
  exact evaluate_functions choice op s f rest after next result
end Itasca.SourceMachine.Stateful

end

/-! ## Bound -/

section

namespace Itasca.SourceMachine.Stateful

theorem transition_bound (bound : Nat) (op : Instruction) (s : store) (ambient : frame)
    (f : AFrame) (rest : List AFrame) (after : List instr) (next : AState)
    (bounded : CodeBound bound ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (step : Transition ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ f rest after op (.next next)) :
    CodeBound bound next := by
  obtain ⟨values,frames,_,_⟩ := transition_frame _ _ _ _ _ _ step
  have functions := transition_functions _ _ _ _ _ _ step
  have active := bounded.frames {f with code := op.source::after} (List.mem_cons_self ..)
  refine ⟨bounded.positive,?_,?_⟩
  · rw [frames]
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · refine ⟨?_,active.2⟩
      have headBound : sizeOf (op.source::after) ≤ bound := active.1
      simp only [List.cons.sizeOf_spec] at headBound
      change sizeOf after ≤ bound
      omega
    · exact bounded.frames frame (List.mem_cons_of_mem _ member)
  · simpa only [functions] using bounded.functions
end Itasca.SourceMachine.Stateful

end

end

end
