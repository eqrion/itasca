import Itasca.Runtime.SourceMachine.Stateful.Signature
import Itasca.Runtime.SourceMachine.Measure
import Itasca.Runtime.SourceMachine.Sim.Structured
import Itasca.Runtime.SourceMachine.Core.Trap
import Itasca.Runtime.Spec.FloatPromote
import Itasca.Runtime.Spec.SegmentInitCases
import Itasca.Runtime.Spec.MemoryGrowth
import Itasca.Runtime.Spec.FloatTrunc

/-!
Sections, each formerly its own module: SignatureTyping, Continuation, TableTyping, MemorySize, ObjectReplacement, PayloadTyping, CopyStore, InitStore, GrowthTyping, MemoryGrow, Reference, ReferenceOperands, TableGrow, TableRead.
-/

/-! ## SignatureTyping -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

private theorem lookup_eq {α : Type} [Inhabited α] (values : List α) (index : Nat) (value : α)
    (bound : index < values.length) (read : values[index]! = value) : values[index]? = some value := by
  simpa only [getElem!_pos values index bound, List.getElem?_eq_getElem bound] using congrArg some read

theorem Signature.of_typed {C : context} {op : Instruction} {input output : List valtype}
    (typed : Instr_ok C op.source ⟨.mk_list input,.mk_list output⟩) : Signature C op input output := by
  cases op <;> simp only [Instruction.source] at typed <;> cases typed
  all_goals first
    | constructor
  all_goals first
    | assumption
    | (apply lookup_eq <;> assumption)

end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## Continuation -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

/-- A typed active instruction exposes its actual operands and the continuation
for any result values of the instruction's generated output type. -/
theorem frame_operands {s : store} {f : AFrame} {op : instr} {code : List instr}
    (typed : FrameTyped s {f with code := op :: code} []) :
    ∃ C front operands inputs outputs,
      ModuleBindings s f.module C ∧ C.LOCALS = f.locals.map valueType ∧
      Instr_ok (labelContext C f.labels) op ⟨.mk_list inputs,.mk_list outputs⟩ ∧
      f.vals = front ++ operands ∧ ResultsTyped s inputs operands ∧
      Forall wf_val front ∧ (∀ label ∈ f.labels, label.height ≤ front.length) ∧
      (∀ produced, ResultsTyped s outputs produced →
        FrameTyped s {f with code := code, vals := front ++ produced} []) := by
  cases typed with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨prefixTypes,inputs,outputs,operation,splitTypes,continuation,heights⟩ :=
      code_stack_after_bounds (value_types_concrete f.vals) hc
    have all : ResultsTyped s (prefixTypes ++ inputs) f.vals := by rw [←splitTypes]; exact values
    obtain ⟨front,operands,split,frontTyped,operandTyped⟩ := results_typed_split all
    refine ⟨C,front,operands,inputs,outputs,bindings,localTypes,operation,split,operandTyped,
      results_typed_wf frontTyped,?_,?_⟩
    · intro label member
      rw [results_typed_length frontTyped]
      exact heights label member
    · intro produced producedTyped
      have typedValues := List.rel_append frontTyped producedTyped
      have resultTypes := results_type_of_typed typedValues
      apply FrameTyped.mk (f := {f with code := code,vals := front ++ produced}) C
        bindings localTypes locals ?_ returns ?_ hw
      · simpa only [ResultsTyped,resultTypes] using typedValues
      · simpa only [List.append_nil,resultTypes] using continuation

end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## TableTyping -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

def tableElementType : tabletype → reftype
  | .mk_tabletype _ type => type

theorem extern_table_lookup {s : store} {address : Nat} {type : tabletype}
    (typed : Externaddr_ok s (.TABLE address) (.TABLE type)) :
    ∃ object, s.TABLES[address]? = some object ∧ tableElementType object.TYPE = tableElementType type := by
  generalize addressEq : externaddr.TABLE address = external at typed
  generalize typeEq : externtype.TABLE type = externalType at typed
  induction typed generalizing type with
  | table a object bound found wf ext =>
    cases addressEq
    cases typeEq
    refine ⟨object,?_,rfl⟩
    simpa [getElem!_pos,bound] using congrArg some found
  | sub external old new typed sub wf oldWf newWf ih =>
    cases sub with
    | table old new relation _ _ =>
      cases typeEq
      cases relation with
      | mk_Tabletype_sub old type new _ _ _ =>
        obtain ⟨object,found,same⟩ := ih (type := .mk_tabletype old type) addressEq rfl
        exact ⟨object,found,same⟩
    | _ => cases typeEq
  | _ => cases addressEq

theorem table_lookup {s : store} {module : moduleinst} {C : context}
    (bindings : ModuleBindings s module C) {index : Nat} {type : tabletype}
    (found : C.TABLES[index]? = some type) :
    ∃ address object, module.TABLES[index]? = some address ∧
      s.TABLES[address]? = some object ∧ tableElementType object.TYPE = tableElementType type := by
  have right := (List.getElem?_eq_some_iff.mp found).1
  have left : index < module.TABLES.length := by rw [bindings.tables.length_eq]; exact right
  have relation := bindings.tables.get left right
  have value := (List.getElem?_eq_some_iff.mp found).2
  simp only [List.get_eq_getElem,value] at relation
  obtain ⟨object,lookup,objectType⟩ := extern_table_lookup relation
  exact ⟨module.TABLES[index],object,List.getElem?_eq_getElem left,lookup,objectType⟩

theorem table_references {s : store} (contents : StoreContentsTyped s) {object : tableinst}
    (member : object ∈ s.TABLES) : Forall (fun value => Ref_ok s value (tableElementType object.TYPE)) object.REFS := by
  have typed := contents.tables object member
  cases typed with
  | mk_Tableinst_ok count maximum type refs typeOk refsOk length _ wf typeWf => exact refsOk

private def minimum : limits → Nat
  | .mk_limits (.mk_uN count) _ => count

private theorem limits_minimum {type : limits} {bound : Nat} (typed : Limits_ok type bound) :
    minimum type ≤ bound := by cases typed; assumption

theorem table_size_bound {s : store} (contents : StoreContentsTyped s) {object : tableinst}
    (member : object ∈ s.TABLES) : object.REFS.length < 2^32 := by
  have typed := contents.tables object member
  cases typed with
  | mk_Tableinst_ok count maximum type refs typeOk refsOk length _ wf typeWf =>
    dsimp only
    rw [length]
    cases typeOk with
    | mk_Tabletype_ok _ _ limits _ =>
      have bound := limits_minimum limits
      change count ≤ _ at bound
      norm_num at bound ⊢
      omega

theorem memory_pages_bound {s : store} (contents : StoreContentsTyped s) {object : meminst}
    (member : object ∈ s.MEMS) : object.BYTES.length / 65536 ≤ 65536 := by
  have typed := contents.memories object member
  cases typed with
  | mk_Meminst_ok count maximum bytes typeOk length _ wf typeWf =>
    dsimp only
    rw [length]
    simp only [Ki]
    norm_num
    cases typeOk with
    | mk_Memtype_ok _ limits _ =>
      have bound := limits_minimum limits
      change count ≤ _ at bound
      norm_num at bound
      exact bound

end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## MemorySize -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

def memorySize (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr) : AResult :=
  match f.module.MEMS[0]? with
  | none => .stuck
  | some address => match s.store.MEMS[address]? with
    | none => .stuck
    | some object => advance s {f with code := after, vals := f.vals ++ [integerVal .I32 (object.BYTES.length / 65536)]} rest

theorem memory_pages_aligned {s : store} (contents : StoreContentsTyped s) {object : meminst}
    (member : object ∈ s.MEMS) : object.BYTES.length % 65536 = 0 := by
  have typed := contents.memories object member
  cases typed with
  | mk_Meminst_ok count maximum bytes typeOk length _ wf typeWf =>
    dsimp only
    rw [length]
    simp [Ki]

theorem memory_size_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .MEMORY_SIZE :: after} :: rest,[]⟩) :
    ∃ next, memorySize ⟨s,ambient,{f with code := .MEMORY_SIZE :: after} :: rest,[]⟩ f rest after = .next next ∧
      CoreTyped next ∧ NextSim ⟨s,ambient,{f with code := .MEMORY_SIZE :: after} :: rest,[]⟩ next := by
  have hf : FrameTyped s {f with code := .MEMORY_SIZE :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | memory_size _ type present selected contextWf typeWf instructionWf =>
    obtain ⟨address,object,mapped,found⟩ := bindings.memory_lookup present
    cases operandTypes
    have sizeBound : object.BYTES.length / 65536 < 2^32 := by
      have bound := memory_pages_bound typed.contents (List.mem_of_getElem? found)
      omega
    have resultTyped := integer_val_typed typed.typed.store .I32 (object.BYTES.length / 65536) sizeBound
    have freshFrame := continuation [integerVal .I32 (object.BYTES.length / 65536)] (.cons resultTyped .nil)
    have actualFrame : FrameTyped s {f with code := after,vals := f.vals ++ [integerVal .I32 (object.BYTES.length / 65536)]} [] := by
      simpa only [split,List.append_nil] using freshFrame
    refine ⟨_,by simp only [memorySize,mapped,found,advance],
      ⟨active_frame_preservation typed.typed actualFrame rfl,typed.contents⟩,NextSim.single ?_⟩
    obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf hf
    have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
    have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
    have memoryEq : fun_mem ⟨s,f.toFrame⟩ (.mk_uN 0) = object := by
      simp [fun_mem,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
    have aligned := memory_pages_aligned typed.contents (List.mem_of_getElem? found)
    have source := Spec.memory_size_step s f.toFrame typed.typed.store frameWf
      (by simpa only [memoryEq] using aligned) (by simpa only [memoryEq] using sizeBound)
    rw [memoryEq] at source
    have height : ∀ label ∈ f.labels, label.height ≤ f.vals.length := by simpa only [split,List.append_nil] using heights
    have full := mutable_stack_simulation s s ambient f rest .MEMORY_SIZE after f.vals []
      [integerVal .I32 (object.BYTES.length / 65536)] typed.typed.ambient labelsWf valuesWf tailWf restWf height
      (by simpa [vals,admininstr_val,integerVal,Segment.i32,numtype_Inn,admininstr_instr] using source)
    simpa only [List.append_nil] using full

end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## ObjectReplacement -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

theorem wf_store_table_set (s : store) (index : Nat) (value : tableinst)
    (old : wf_store s) (fresh : wf_tableinst value) : wf_store {s with TABLES := s.TABLES.set index value} := by
  cases s with | MKstore funcs globals tables memories elements data =>
  cases old with | store_case_ _ _ _ _ _ _ hf hg ht hm hd =>
  refine .store_case_ _ _ _ _ _ _ hf hg ?_ hm hd
  intro table member
  rcases List.mem_or_eq_of_mem_set member with member | rfl
  · exact ht table member
  · exact fresh

theorem wf_store_memory_set (s : store) (index : Nat) (value : meminst)
    (old : wf_store s) (fresh : wf_meminst value) : wf_store {s with MEMS := s.MEMS.set index value} := by
  cases s with | MKstore funcs globals tables memories elements data =>
  cases old with | store_case_ _ _ _ _ _ _ hf hg ht hm hd =>
  refine .store_case_ _ _ _ _ _ _ hf hg ht ?_ hd
  intro memory member
  rcases List.mem_or_eq_of_mem_set member with member | rfl
  · exact hm memory member
  · exact fresh

theorem table_replacement_preserves (s : store) (index : Nat) (old fresh : tableinst)
    (wf : wf_store s) (contents : StoreContentsTyped s) (found : s.TABLES[index]? = some old)
    (extension : Extend_tableinst old fresh) (typed : Tableinst_ok s fresh fresh.TYPE) :
    Extend_store s {s with TABLES := s.TABLES.set index fresh} ∧
      StoreContentsTyped {s with TABLES := s.TABLES.set index fresh} := by
  have objectWf : wf_tableinst fresh := by cases typed; assumption
  have freshWf := wf_store_table_set s index fresh wf objectWf
  have extended : Extend_store s {s with TABLES := s.TABLES.set index fresh} := by
    apply extend_store_set_table _ _ _ wf freshWf
    intro bound
    simpa only [List.getElem!_eq_getElem?_getD,found,Option.getD_some] using extension
  refine ⟨extended,?_,?_,?_,?_,?_⟩
  · exact fun item member => globalinst_typed_extend extended (contents.globals item member)
  · intro item member
    rcases List.mem_or_eq_of_mem_set member with member | rfl
    · exact tableinst_typed_extend extended (contents.tables item member)
    · exact tableinst_typed_extend extended typed
  · exact fun item member => meminst_typed_extend extended (contents.memories item member)
  · exact fun item member => eleminst_ok_extend extended (extend_elem_refl item) (contents.elements item member)
  · intro item member
    have entryTyped := contents.data item member
    have entryWf : wf_datainst item := by cases entryTyped; assumption
    exact datainst_ok_extend extended (extend_data_refl item entryWf) entryTyped

theorem memory_replacement_preserves (s : store) (index : Nat) (old fresh : meminst)
    (wf : wf_store s) (contents : StoreContentsTyped s) (found : s.MEMS[index]? = some old)
    (extension : Extend_meminst old fresh) (typed : Meminst_ok s fresh fresh.TYPE) :
    Extend_store s {s with MEMS := s.MEMS.set index fresh} ∧
      StoreContentsTyped {s with MEMS := s.MEMS.set index fresh} := by
  have objectWf : wf_meminst fresh := by cases typed; assumption
  have freshWf := wf_store_memory_set s index fresh wf objectWf
  have extended : Extend_store s {s with MEMS := s.MEMS.set index fresh} := by
    apply extend_store_set_mem _ _ _ wf freshWf
    intro bound
    simpa only [List.getElem!_eq_getElem?_getD,found,Option.getD_some] using extension
  refine ⟨extended,contents.memory_replacement extended index fresh rfl rfl rfl rfl rfl ?_⟩
  exact meminst_typed_extend extended typed
end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## PayloadTyping -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

theorem copy_into_forall {T : Type} [Inhabited T] (property : T → Prop)
    (before source : List T) (destination offset count : Nat)
    (old : Forall property before) (values : Forall property source)
    (inside : offset+count ≤ source.length) :
    Forall property (Segment.copyInto before source destination offset count) := by
  induction count generalizing before destination offset with
  | zero => exact old
  | succ count ih =>
    apply ih (before.set destination source[offset]!) (destination+1) (offset+1) _ (by omega)
    intro value member
    rcases List.mem_or_eq_of_mem_set member with member | rfl
    · exact old value member
    · exact values source[offset]! (by rw [getElem!_pos source offset (by omega)]; exact List.getElem_mem (by omega))

theorem table_payload_typed {s : store} {object : tableinst} (typed : Tableinst_ok s object object.TYPE)
    (values : List ref) (length : values.length = object.REFS.length)
    (refs : Forall (fun value => Ref_ok s value (tableElementType object.TYPE)) values) :
    Tableinst_ok s {object with REFS := values} object.TYPE ∧
      Extend_tableinst object {object with REFS := values} := by
  cases typed with
  | mk_Tableinst_ok count maximum type old typeOk oldRefs oldLength storeWf objectWf typeWf =>
    refine ⟨.mk_Tableinst_ok _ _ _ _ _ typeOk refs ?_ storeWf (.tableinst_case_ _ _ typeWf) typeWf,?_⟩
    · exact length.trans oldLength
    · exact extend_table_contents count count maximum type old values (by rfl) (by simpa only using length.ge) objectWf (.tableinst_case_ _ _ typeWf)

theorem memory_payload_typed {s : store} {object : meminst} (typed : Meminst_ok s object object.TYPE)
    (bytes : List byte) (length : bytes.length = object.BYTES.length) (values : Forall wf_byte bytes) :
    Meminst_ok s {object with BYTES := bytes} object.TYPE ∧
      Extend_meminst object {object with BYTES := bytes} := by
  cases typed with
  | mk_Meminst_ok count maximum old typeOk oldLength storeWf objectWf typeWf =>
    refine ⟨.mk_Meminst_ok _ _ _ _ typeOk ?_ storeWf (.meminst_case_ _ _ typeWf values) typeWf,?_⟩
    · exact length.trans oldLength
    · exact extend_mem_contents count count maximum old bytes (by rfl) (by simpa only using length.ge) objectWf (.meminst_case_ _ _ typeWf values)
end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## CopyStore -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

theorem memory_copy_preserves (s : store) (f : frame) (address destination source count : Nat)
    (object : meminst) (wf : wf_store s) (contents : StoreContentsTyped s)
    (mapped : f.MODULE.MEMS[0]? = some address) (found : s.MEMS[address]? = some object)
    (inside : source+count ≤ object.BYTES.length ∧ destination+count ≤ object.BYTES.length) :
    Extend_store s (Segment.memoryCopy s f destination source count) ∧
      StoreContentsTyped (Segment.memoryCopy s f destination source count) := by
  have typed := contents.memories object (List.mem_of_getElem? found)
  have bytes : Forall wf_byte object.BYTES := by
    have objectWf : wf_meminst object := by cases typed; assumption
    cases objectWf; assumption
  have copied := copy_into_forall wf_byte object.BYTES object.BYTES destination source count bytes bytes inside.1
  have length := Segment.copy_into_length object.BYTES object.BYTES destination source count
  rw [Segment.copy_into_eq_set_slice _ _ _ _ _ inside.1 inside.2] at copied length
  obtain ⟨newTyped,objectExtension⟩ := memory_payload_typed typed _ length copied
  have result := memory_replacement_preserves s address object _ wf contents found objectExtension newTyped
  simpa only [Segment.memoryCopy,Segment.withBytes,List.getElem!_eq_getElem?_getD,mapped,found,Option.getD_some] using result

theorem table_copy_preserves (s : store) (f : frame) (targetTable sourceTable targetAddress sourceAddress destination source count : Nat)
    (targetObject sourceObject : tableinst) (wf : wf_store s) (contents : StoreContentsTyped s)
    (targetMapped : f.MODULE.TABLES[targetTable]? = some targetAddress)
    (sourceMapped : f.MODULE.TABLES[sourceTable]? = some sourceAddress)
    (targetFound : s.TABLES[targetAddress]? = some targetObject) (sourceFound : s.TABLES[sourceAddress]? = some sourceObject)
    (sameType : tableElementType targetObject.TYPE = tableElementType sourceObject.TYPE)
    (inside : source+count ≤ sourceObject.REFS.length ∧ destination+count ≤ targetObject.REFS.length) :
    Extend_store s (Segment.tableCopy s f targetTable sourceTable destination source count) ∧
      StoreContentsTyped (Segment.tableCopy s f targetTable sourceTable destination source count) := by
  have typed := contents.tables targetObject (List.mem_of_getElem? targetFound)
  have old := table_references contents (List.mem_of_getElem? targetFound)
  have fresh := table_references contents (List.mem_of_getElem? sourceFound)
  rw [←sameType] at fresh
  have copied := copy_into_forall _ targetObject.REFS sourceObject.REFS destination source count old fresh inside.1
  have length := Segment.copy_into_length targetObject.REFS sourceObject.REFS destination source count
  rw [Segment.copy_into_eq_set_slice _ _ _ _ _ inside.1 inside.2] at copied length
  obtain ⟨newTyped,objectExtension⟩ := table_payload_typed typed _ length copied
  have result := table_replacement_preserves s targetAddress targetObject _ wf contents targetFound objectExtension newTyped
  simpa only [Segment.tableCopy,Segment.withRefs,List.getElem!_eq_getElem?_getD,targetMapped,sourceMapped,
    targetFound,sourceFound,Option.getD_some] using result
end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## InitStore -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

theorem memory_byte_length_bound {s : store} (contents : StoreContentsTyped s) {object : meminst}
    (member : object ∈ s.MEMS) : object.BYTES.length ≤ 2^32 := by
  have pages := memory_pages_bound contents member
  have aligned := memory_pages_aligned contents member
  have division := Nat.mod_add_div object.BYTES.length 65536
  omega

theorem data_bytes_typed {s : store} {object : datainst} (typed : Datainst_ok s object .OK) :
    object.BYTES.length < 2^32 ∧ Forall wf_byte object.BYTES := by
  cases typed with
  | mk_Datainst_ok bytes bound wf objectWf =>
    exact ⟨bound,by cases objectWf; assumption⟩

theorem element_refs_typed {s : store} {object : eleminst} {type : reftype} (typed : Eleminst_ok s object type) :
    object.TYPE = type ∧ object.REFS.length < 2^32 ∧ Forall (fun value => Ref_ok s value type) object.REFS := by
  cases typed with
  | mk_Eleminst_ok type refs refsOk bound wf => exact ⟨rfl,bound,refsOk⟩

theorem memory_init_preserves (s : store) (f : frame) (address dataIndex dataAddress destination source count : Nat)
    (object : meminst) (data : datainst) (wf : wf_store s) (contents : StoreContentsTyped s)
    (mapped : f.MODULE.MEMS[0]? = some address) (found : s.MEMS[address]? = some object)
    (dataMapped : f.MODULE.DATAS[dataIndex]? = some dataAddress) (dataFound : s.DATAS[dataAddress]? = some data)
    (inside : source+count ≤ data.BYTES.length ∧ destination+count ≤ object.BYTES.length) :
    Extend_store s (Segment.memoryInit s f dataIndex destination source count) ∧
      StoreContentsTyped (Segment.memoryInit s f dataIndex destination source count) ∧
      (Segment.memoryInit s f dataIndex destination source count).FUNCS = s.FUNCS := by
  have typed := contents.memories object (List.mem_of_getElem? found)
  have bytes : Forall wf_byte object.BYTES := by
    have objectWf : wf_meminst object := by cases typed; assumption
    cases objectWf; assumption
  obtain ⟨dataBound,dataBytes⟩ := data_bytes_typed (contents.data data (List.mem_of_getElem? dataFound))
  have copied := copy_into_forall wf_byte object.BYTES data.BYTES destination source count bytes dataBytes inside.1
  have length := Segment.copy_into_length object.BYTES data.BYTES destination source count
  obtain ⟨newTyped,objectExtension⟩ := memory_payload_typed typed _ length copied
  have result := memory_replacement_preserves s address object _ wf contents found objectExtension newTyped
  have memoryEq : fun_mem ⟨s,f⟩ (.mk_uN 0) = object := by simp [fun_mem,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
  have dataEq : fun_data ⟨s,f⟩ (.mk_uN dataIndex) = data := by simp [fun_data,proj_uN_0,List.getElem!_eq_getElem?_getD,dataMapped,dataFound]
  have memoryBound := memory_byte_length_bound contents (List.mem_of_getElem? found)
  have addressBound : f.MODULE.MEMS[0]! < s.MEMS.length := by
    simpa only [List.getElem!_eq_getElem?_getD,mapped,Option.getD_some] using (List.getElem?_eq_some_iff.mp found).1
  have final := Segment.memory_init_eq s f dataIndex destination source count addressBound
    (by simpa only [memoryEq] using memoryBound) (by simpa only [dataEq] using dataBound.le)
    (by simpa only [memoryEq,dataEq] using inside)
  simp only [dataEq,List.getElem!_eq_getElem?_getD,mapped,Option.getD_some,List.modify_eq_set_getElem?,found,Option.map_some] at final
  rw [final]
  exact ⟨result.1,result.2,rfl⟩

theorem table_init_preserves (s : store) (f : frame) (tableIndex elementIndex tableAddress elementAddress destination source count : Nat)
    (object : tableinst) (element : eleminst) (wf : wf_store s) (contents : StoreContentsTyped s)
    (mapped : f.MODULE.TABLES[tableIndex]? = some tableAddress) (found : s.TABLES[tableAddress]? = some object)
    (elementMapped : f.MODULE.ELEMS[elementIndex]? = some elementAddress) (elementFound : s.ELEMS[elementAddress]? = some element)
    (sameType : tableElementType object.TYPE = element.TYPE)
    (inside : source+count ≤ element.REFS.length ∧ destination+count ≤ object.REFS.length) :
    Extend_store s (Segment.tableInit s f tableIndex elementIndex destination source count) ∧
      StoreContentsTyped (Segment.tableInit s f tableIndex elementIndex destination source count) ∧
      (Segment.tableInit s f tableIndex elementIndex destination source count).FUNCS = s.FUNCS := by
  have typed := contents.tables object (List.mem_of_getElem? found)
  have refs := table_references contents (List.mem_of_getElem? found)
  obtain ⟨_,elementBound,elementRefs⟩ := element_refs_typed (contents.elements element (List.mem_of_getElem? elementFound))
  rw [←sameType] at elementRefs
  have copied := copy_into_forall _ object.REFS element.REFS destination source count refs elementRefs inside.1
  have length := Segment.copy_into_length object.REFS element.REFS destination source count
  obtain ⟨newTyped,objectExtension⟩ := table_payload_typed typed _ length copied
  have result := table_replacement_preserves s tableAddress object _ wf contents found objectExtension newTyped
  have elementEq : fun_elem ⟨s,f⟩ (.mk_uN elementIndex) = element := by simp [fun_elem,proj_uN_0,List.getElem!_eq_getElem?_getD,elementMapped,elementFound]
  have final := Segment.table_init_eq s f tableIndex elementIndex destination source count
  simp only [elementEq,List.getElem!_eq_getElem?_getD,mapped,Option.getD_some,List.modify_eq_set_getElem?,found,Option.map_some] at final
  rw [final]
  exact ⟨result.1,result.2,rfl⟩
end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## GrowthTyping -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

def limitMaximum : limits → Option Nat
  | .mk_limits _ maximum => maximum.map proj_uN_0

theorem limits_maximum_bound {type : limits} {bound : Nat} (typed : Limits_ok type bound) :
    ∀ maximum ∈ limitMaximum type, maximum ≤ bound := by
  cases typed with
  | mk_Limits_ok minimum maximum bound low high wf =>
    cases maximum with
    | none => simp [limitMaximum,OMap]
    | some maximum =>
      simpa [limitMaximum,OMap,proj_uN_0] using (high maximum (by simp)).2

theorem limits_grown {old count bound : Nat} {maximum : Option Nat}
    (typed : Limits_ok (.mk_limits (.mk_uN old) (OMap uN.mk_uN maximum)) bound)
    (small : count ≤ bound) (within : Forall (fun limit => count ≤ limit) maximum.toList)
    (wf : wf_limits (.mk_limits (.mk_uN count) (OMap uN.mk_uN maximum))) :
    Limits_ok (.mk_limits (.mk_uN count) (OMap uN.mk_uN maximum)) bound := by
  apply Limits_ok.mk_Limits_ok count maximum bound small _ wf
  intro limit member
  refine ⟨within limit member,?_⟩
  apply limits_maximum_bound typed limit
  cases maximum with
  | none => simp at member
  | some maximum => simpa [limitMaximum,OMap,proj_uN_0,eq_comm] using member

theorem growtable_typed {s : store} {object next : tableinst} {delta : Nat} {value : ref}
    (typed : Tableinst_ok s object object.TYPE)
    (valueTyped : Ref_ok s value (tableElementType object.TYPE))
    (grown : fun_growtable object delta value (some next)) :
    Tableinst_ok s next next.TYPE ∧ Extend_tableinst object next := by
  cases grown with
  | fun_growtable_case_0 _ minimum maximum type refs count source size limit target freshWf oldWf targetWf =>
    subst object
    subst next
    subst count
    cases typed with
    | mk_Tableinst_ok old max type refs typeOk refsOk length storeWf objectWf typeWf =>
      have small : refs.length+delta < 2^32 := by
        cases targetWf with | tableinst_case_ _ _ tableWf =>
        cases tableWf with | tabletype_case_0 _ _ limitsWf =>
        cases limitsWf with | limits_case_0 _ _ minWf _ =>
        cases minWf with | uN_case_0 _ bound => norm_num at bound ⊢; omega
      have wfLimits : wf_limits (.mk_limits (.mk_uN (refs.length+delta)) (OMap uN.mk_uN max)) := by
        cases targetWf; rename_i tableWf; cases tableWf; assumption
      have limitsOk : Limits_ok (.mk_limits (.mk_uN old) (OMap uN.mk_uN max)) (Int.toNat (((2^32):Int)-1)) := by
        cases typeOk; assumption
      have countLimit : Forall (fun maximum => refs.length+delta ≤ maximum) max.toList := by
        cases max <;> simpa [Forall,OMap,proj_uN_0] using limit
      have newLimits := limits_grown limitsOk (count:=refs.length+delta) (by norm_num; omega) countLimit wfLimits
      have newTableWf : wf_tabletype (.mk_tabletype (.mk_limits (.mk_uN (refs.length+delta)) (OMap uN.mk_uN max)) type) :=
        .tabletype_case_0 _ _ wfLimits
      constructor
      · apply Tableinst_ok.mk_Tableinst_ok s (refs.length+delta) max type (refs++List.replicate delta value)
          (.mk_Tabletype_ok _ _ newLimits newTableWf)
        · intro reference member
          rcases List.mem_append.mp member with original | added
          · exact refsOk reference original
          · have same : reference=value := List.eq_of_mem_replicate added
            subst reference
            exact valueTyped
        · simp
        · exact storeWf
        · exact targetWf
        · exact newTableWf
      · exact extend_table_contents old (refs.length+delta) max type refs (refs++List.replicate delta value)
          (by omega) (by simp) objectWf targetWf


theorem growmemory_typed {s : store} {object next : meminst} {delta : Nat}
    (typed : Meminst_ok s object object.TYPE)
    (grown : fun_growmemory object delta (some next)) :
    Meminst_ok s next next.TYPE ∧ Extend_meminst object next := by
  cases grown with
  | fun_growmemory_case_0 _ minimum maximum bytes count source size limit small target freshWf oldWf targetWf =>
    subst object
    subst next
    cases typed with
    | mk_Meminst_ok old max bytes typeOk length storeWf objectWf typeWf =>
      have countEq : count = ((old+delta : Nat) : Rat) := by
        rw [size,length]
        norm_num [Ki,Nat.cast_mul,Nat.cast_add]
      rw [countEq] at limit small freshWf targetWf ⊢
      have natural : rat_to_nat (((old+delta : Nat) : Rat)) = old+delta := by
        simp only [rat_to_nat,Rat.num_natCast,Rat.den_natCast]
        change ((Int.ofNat (old+delta)).tdiv 1).toNat = old+delta
        rw [Int.tdiv_one]
        rfl
      rw [natural] at freshWf targetWf ⊢
      have smallNat : old+delta ≤ 2^16 := by exact_mod_cast small
      have wfLimits : wf_limits (.mk_limits (.mk_uN (old+delta)) (OMap uN.mk_uN max)) := by
        cases targetWf; rename_i memoryWf _; cases memoryWf; assumption
      have limitsOk : Limits_ok (.mk_limits (.mk_uN old) (OMap uN.mk_uN max)) (2^16) := by
        cases typeOk; assumption
      have countLimit : Forall (fun maximum => old+delta ≤ maximum) max.toList := by
        cases max with
        | none => simp [Forall]
        | some max =>
          have one := limit (.mk_uN max) (by simp [OMap])
          have bounded : old+delta ≤ max := by exact_mod_cast one
          simpa [Forall] using bounded
      have newLimits := limits_grown limitsOk smallNat countLimit wfLimits
      have newMemoryWf : wf_memtype (.PAGE (.mk_limits (.mk_uN (old+delta)) (OMap uN.mk_uN max))) :=
        .memtype_case_0 _ wfLimits
      constructor
      · exact .mk_Meminst_ok s (old+delta) max (bytes++List.replicate (delta*(64*Ki)) (.mk_byte 0))
          (.mk_Memtype_ok _ newLimits newMemoryWf)
          (by simp only [List.length_append,List.length_replicate,length,Nat.add_mul])
          storeWf targetWf newMemoryWf
      · exact extend_mem_contents old (old+delta) max bytes (bytes++List.replicate (delta*(64*Ki)) (.mk_byte 0))
          (by omega) (by simp) objectWf targetWf
end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## MemoryGrow -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

/-- Refusal is permitted independently of the pure successful-growth rule. -/
inductive MemoryGrowthChoice (before : meminst) (delta : Nat) : Option meminst → Prop
  | refused : MemoryGrowthChoice before delta none
  | grown {next} : fun_growmemory before delta (some next) → MemoryGrowthChoice before delta (some next)

def memoryGrow (choice : Option meminst) (s : AState) (f : AFrame) (rest : List AFrame)
    (after : List instr) : AResult :=
  match pop f.vals, f.module.MEMS[0]? with
  | some (front,value), some address => match integer .I32 value, s.store.MEMS[address]? with
    | some _, some object => match choice with
      | none => advance s {f with code := after,vals := front++[integerVal .I32 (2^32-1)]} rest
      | some next => advance {s with store := {s.store with MEMS := s.store.MEMS.set address next}}
          {f with code := after,vals := front++[integerVal .I32 (object.BYTES.length/65536)]} rest
    | _,_ => .stuck
  | _,_ => .stuck

theorem memory_grow_choices (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .MEMORY_GROW::after}::rest,[]⟩) :
    ∃ front delta address object,
      f.vals = front++[integerVal .I32 delta] ∧ f.module.MEMS[0]? = some address ∧ s.MEMS[address]? = some object ∧
      ∀ choice, MemoryGrowthChoice object delta choice →
      ∃ next, memoryGrow choice ⟨s,ambient,{f with code := .MEMORY_GROW::after}::rest,[]⟩ f rest after = .next next ∧
        CoreTyped next ∧ Extend_store s next.store ∧
        NextSim ⟨s,ambient,{f with code := .MEMORY_GROW::after}::rest,[]⟩ next := by
  have hf : FrameTyped s {f with code := .MEMORY_GROW::after} [] := by cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | memory_grow _ type present selected contextWf typeWf instructionWf =>
    obtain ⟨address,object,mapped,found⟩ := bindings.memory_lookup present
    cases operandTypes with
    | cons valueTyped tail =>
      cases tail
      obtain ⟨delta,rfl,deltaBound⟩ := integer_val_inv (ty:=.I32) valueTyped
      have decoded : integer .I32 (integerVal .I32 delta) = some delta := integer_accepts .I32 delta deltaBound
      refine ⟨front,delta,address,object,split,mapped,found,?_⟩
      intro choice allowed
      obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf hf
      have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
      have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
      cases allowed with
      | refused =>
        have resultTyped := integer_val_typed typed.typed.store .I32 (2^32-1) (by decide)
        have freshFrame := continuation [integerVal .I32 (2^32-1)] (.cons resultTyped .nil)
        refine ⟨_,by simp only [memoryGrow,split,pop_append,mapped,decoded,found,advance],
          ⟨active_frame_preservation typed.typed freshFrame rfl,typed.contents⟩,extend_store_refl _ typed.typed.store,NextSim.single ?_⟩
        have source := memory_grow_fail_step s f.toFrame delta typed.typed.store frameWf deltaBound
        have full := mutable_stack_simulation s s ambient f rest .MEMORY_GROW after front [integerVal .I32 delta]
          [integerVal .I32 (2^32-1)] typed.typed.ambient labelsWf frontWf tailWf restWf heights
          (by simpa [AFrame.toFrame,vals,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
        simpa only [split] using full
      | @grown grownObject grown =>
        have objectTyped := typed.contents.memories object (List.mem_of_getElem? found)
        obtain ⟨newTyped,objectExtension⟩ := growmemory_typed objectTyped grown
        obtain ⟨extension,contents⟩ := memory_replacement_preserves s address object grownObject typed.typed.store typed.contents found objectExtension newTyped
        have bound : object.BYTES.length/65536 < 2^32 := by
          have := memory_pages_bound typed.contents (List.mem_of_getElem? found); omega
        have resultTyped := integer_val_typed typed.typed.store .I32 (object.BYTES.length/65536) bound
        have frameNext := continuation [integerVal .I32 (object.BYTES.length/65536)] (.cons resultTyped .nil)
        have fresh := (active_frame_preservation typed.typed frameNext rfl).extend_same extension rfl
        refine ⟨_,by simp only [memoryGrow,split,pop_append,mapped,decoded,found,advance],⟨fresh,contents⟩,extension,NextSim.single ?_⟩
        have memoryEq : fun_mem ⟨s,f.toFrame⟩ (.mk_uN 0) = object := by
          simp [fun_mem,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
        have storeEq : {s with MEMS := s.MEMS.modify f.module.MEMS[0]! (fun _ => grownObject)} =
            {s with MEMS := s.MEMS.set address grownObject} := by
          simp [List.getElem!_eq_getElem?_getD,mapped,Option.getD_some,List.modify_eq_set_getElem?,found]
        have source := memory_grow_success_step s f.toFrame delta grownObject typed.typed.store frameWf deltaBound
          (List.getElem?_eq_some_iff.mp mapped).1 (by simpa only [memoryEq] using bound)
          (by simpa only [memoryEq] using grown) (by simpa only [AFrame.toFrame,storeEq] using (extend_store_wf extension).2)
        rw [memoryEq] at source
        simp only [AFrame.toFrame,storeEq] at source
        have full := mutable_stack_simulation s {s with MEMS:=s.MEMS.set address grownObject} ambient f rest .MEMORY_GROW after front
          [integerVal .I32 delta] [integerVal .I32 (object.BYTES.length/65536)] typed.typed.ambient labelsWf frontWf tailWf restWf heights
          (by simpa [AFrame.toFrame,vals,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
        simpa only [split] using full
end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## Reference -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

def asReference : val → Option ref
  | .REF_NULL ty => some (.REF_NULL ty)
  | .REF_FUNC_ADDR address => some (.REF_FUNC_ADDR address)
  | .REF_HOST_ADDR address => some (.REF_HOST_ADDR address)
  | _ => none

@[simp] theorem as_reference_value (value : ref) : asReference (val_ref value) = some value := by
  cases value <;> rfl

def refNull (s : AState) (f : AFrame) (rest : List AFrame) (type : reftype) (after : List instr) : AResult :=
  advance s {f with code := after,vals := f.vals ++ [.REF_NULL type]} rest

def refFunc (s : AState) (f : AFrame) (rest : List AFrame) (index : Nat) (after : List instr) : AResult :=
  match f.module.FUNCS[index]? with
  | none => .stuck
  | some address => advance s {f with code := after,vals := f.vals ++ [.REF_FUNC_ADDR address]} rest

def refIsNull (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr) : AResult :=
  match pop f.vals with
  | none => .stuck
  | some (front,value) => match asReference value with
    | none => .stuck
    | some reference => advance s {f with code := after, vals := front ++ [integerVal .I32 (Spec.referenceIsNull reference)]} rest

theorem ref_null_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (type : reftype) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .REF_NULL type :: after} :: rest,[]⟩) :
    ∃ next, refNull ⟨s,ambient,{f with code := .REF_NULL type :: after} :: rest,[]⟩ f rest type after = .next next ∧
      CoreTyped next ∧ NextSim ⟨s,ambient,{f with code := .REF_NULL type :: after} :: rest,[]⟩ next := by
  have hf : FrameTyped s {f with code := .REF_NULL type :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation
  cases operandTypes
  have valueTyped : Val_ok s (.REF_NULL type) (valtype_reftype type) :=
    .reftype s (.REF_NULL type) type (.null s type typed.typed.store) typed.typed.store
  have freshFrame := continuation [.REF_NULL type] (.cons valueTyped .nil)
  have actualFrame : FrameTyped s {f with code := after,vals := f.vals ++ [.REF_NULL type]} [] := by
    simpa only [split,List.append_nil] using freshFrame
  refine ⟨_,rfl,⟨active_frame_preservation typed.typed actualFrame rfl,typed.contents⟩,Or.inl ⟨?_,?_⟩⟩
  · have height : ∀ label ∈ f.labels, label.height ≤ f.vals.length := by simpa only [split,List.append_nil] using heights
    simp only [decode,decodeFrames,vals,List.map_nil,List.nil_append,AFrame.toFrame,List.map_cons,admininstr_instr]
    rw [decode_labels_move_values _ _ _ _ height]
    rfl
  · simp [administrativeMeasure]

theorem ref_func_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .REF_FUNC (.mk_uN index) :: after} :: rest,[]⟩) :
    ∃ next, refFunc ⟨s,ambient,{f with code := .REF_FUNC (.mk_uN index) :: after} :: rest,[]⟩ f rest index after = .next next ∧
      CoreTyped next ∧ NextSim ⟨s,ambient,{f with code := .REF_FUNC (.mk_uN index) :: after} :: rest,[]⟩ next := by
  have hf : FrameTyped s {f with code := .REF_FUNC (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | ref_func _ _ functionType bound sourceType contextWf instructionWf =>
    cases operandTypes
    simp only [labelContext,proj_uN_0] at bound sourceType
    have mappedBound : index < f.module.FUNCS.length := by rw [bindings.funcs.length_eq]; exact bound
    obtain ⟨fn,found,fnType⟩ := bindings.funcs.get mappedBound bound
    simp only [List.get_eq_getElem] at found fnType
    let address := f.module.FUNCS[index]
    have mapped : f.module.FUNCS[index]? = some address := List.getElem?_eq_getElem mappedBound
    have issued : address < s.FUNCS.length := (List.getElem?_eq_some_iff.mp found).1
    have reference : Ref_ok s (.REF_FUNC_ADDR address) .FUNCREF := by
      apply Ref_ok.func s address (s.FUNCS[address]!).TYPE
      · exact .func s address _ issued rfl typed.typed.store (.externtype_case_0 _)
      · exact typed.typed.store
      · exact .externtype_case_0 _
    have valueTyped : Val_ok s (.REF_FUNC_ADDR address) .FUNCREF := .reftype s _ _ reference typed.typed.store
    have freshFrame := continuation [.REF_FUNC_ADDR address] (.cons valueTyped .nil)
    have actualFrame : FrameTyped s {f with code := after,vals := f.vals ++ [.REF_FUNC_ADDR address]} [] := by
      simpa only [split,List.append_nil] using freshFrame
    refine ⟨_,by simp only [refFunc,mapped,advance],
      ⟨active_frame_preservation typed.typed actualFrame rfl,typed.contents⟩,NextSim.single ?_⟩
    obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf hf
    have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
    have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
    have indexBound : index < 2^32 := by cases instructionWf <;> rename_i valid; cases valid <;> norm_num at * <;> omega
    have source := Spec.ref_func_step s f.toFrame index address typed.typed.store frameWf indexBound mapped
    have height : ∀ label ∈ f.labels, label.height ≤ f.vals.length := by simpa only [split,List.append_nil] using heights
    simpa [vals,admininstr_instr] using mutable_stack_simulation s s ambient f rest
      (.REF_FUNC (.mk_uN index)) after f.vals [] [.REF_FUNC_ADDR address] typed.typed.ambient labelsWf valuesWf tailWf restWf height source

private theorem reference_value {s : store} {value : val} {type : reftype}
    (typed : Val_ok s value (valtype_reftype type)) : ∃ reference, value = val_ref reference := by
  generalize equation : valtype_reftype type = actual at typed
  cases typed with
  | numtype nt _ _ _ => cases type <;> cases nt <;> cases equation
  | vectype vt _ _ _ => cases type <;> cases vt <;> cases equation
  | reftype value type _ _ => exact ⟨value,rfl⟩

theorem ref_is_null_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .REF_IS_NULL :: after} :: rest,[]⟩) :
    ∃ next, refIsNull ⟨s,ambient,{f with code := .REF_IS_NULL :: after} :: rest,[]⟩ f rest after = .next next ∧
      CoreTyped next ∧ NextSim ⟨s,ambient,{f with code := .REF_IS_NULL :: after} :: rest,[]⟩ next := by
  have hf : FrameTyped s {f with code := .REF_IS_NULL :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | ref_is_null _ type contextWf instructionWf =>
    cases operandTypes with
    | cons valueTyped tail =>
      cases tail
      obtain ⟨reference,rfl⟩ := reference_value valueTyped
      have bound : Spec.referenceIsNull reference < 2^32 := by cases reference <;> simp [Spec.referenceIsNull]
      have resultTyped := integer_val_typed typed.typed.store .I32 (Spec.referenceIsNull reference) bound
      have freshFrame := continuation [integerVal .I32 (Spec.referenceIsNull reference)] (.cons resultTyped .nil)
      refine ⟨_,by simp only [refIsNull,split,pop_append,as_reference_value,advance],
        ⟨active_frame_preservation typed.typed freshFrame rfl,typed.contents⟩,NextSim.single ?_⟩
      obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf hf
      have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
      have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
      have source := Spec.ref_is_null_step s f.toFrame reference typed.typed.store frameWf
      have source' : StepH ⟨⟨s,f.toFrame⟩,vals [val_ref reference] ++ [admininstr_instr .REF_IS_NULL]⟩ []
          ⟨⟨s,f.toFrame⟩,vals [integerVal .I32 (Spec.referenceIsNull reference)]⟩ := by
        cases reference <;>
          simpa only [vals,List.map_cons,List.map_nil,List.singleton_append,val_ref,admininstr_ref,admininstr_instr,
            integerVal,numtype_Inn,admininstr_val,Segment.i32] using source
      simpa only [split] using mutable_stack_simulation s s ambient f rest .REF_IS_NULL after front
        [val_ref reference] [integerVal .I32 (Spec.referenceIsNull reference)]
        typed.typed.ambient labelsWf frontWf tailWf restWf heights source'

end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## ReferenceOperands -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

theorem reference_operand {s : store} {value : val} {type : reftype}
    (typed : Val_ok s value (valtype_reftype type)) :
    ∃ reference, value = val_ref reference ∧ Ref_ok s reference type := by
  generalize equation : valtype_reftype type = actual at typed
  cases typed with
  | numtype nt _ _ _ => cases type <;> cases nt <;> cases equation
  | vectype vt _ _ _ => cases type <;> cases vt <;> cases equation
  | reftype reference actualType referenceTyped _ =>
    have same : actualType = type := by cases type <;> cases actualType <;> simp_all [valtype_reftype]
    subst actualType
    exact ⟨reference,rfl,referenceTyped⟩

@[simp] theorem reference_admin_value (value : ref) : admininstr_val (val_ref value) = admininstr_ref value := by
  cases value <;> rfl
end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## TableGrow -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

/-- Refusal is permitted independently of the pure successful-growth rule. -/
inductive TableGrowthChoice (before : tableinst) (delta : Nat) (value : ref) : Option tableinst → Prop
  | refused : TableGrowthChoice before delta value none
  | grown {next} : fun_growtable before delta value (some next) → TableGrowthChoice before delta value (some next)

def tableGrow (choice : Option tableinst) (s : AState) (f : AFrame) (rest : List AFrame)
    (index : Nat) (after : List instr) : AResult :=
  match pop f.vals, f.module.TABLES[index]? with
  | some (first,size), some address => match pop first, integer .I32 size, s.store.TABLES[address]? with
    | some (front,value), some _, some object => match asReference value with
      | none => .stuck
      | some _ => match choice with
        | none => advance s {f with code := after,vals := front++[integerVal .I32 (2^32-1)]} rest
        | some next => advance {s with store := {s.store with TABLES := s.store.TABLES.set address next}}
            {f with code := after,vals := front++[integerVal .I32 object.REFS.length]} rest
    | _,_,_ => .stuck
  | _,_ => .stuck

theorem table_grow_choices (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .TABLE_GROW (.mk_uN index)::after}::rest,[]⟩) :
    ∃ front reference delta address object,
      f.vals = front++[val_ref reference,integerVal .I32 delta] ∧ f.module.TABLES[index]? = some address ∧ s.TABLES[address]? = some object ∧
      ∀ choice, TableGrowthChoice object delta reference choice →
      ∃ next, tableGrow choice ⟨s,ambient,{f with code := .TABLE_GROW (.mk_uN index)::after}::rest,[]⟩ f rest index after = .next next ∧
        CoreTyped next ∧ Extend_store s next.store ∧
        NextSim ⟨s,ambient,{f with code := .TABLE_GROW (.mk_uN index)::after}::rest,[]⟩ next := by
  have hf : FrameTyped s {f with code := .TABLE_GROW (.mk_uN index)::after} [] := by cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | table_grow _ _ type limits bound selected contextWf instructionWf =>
    have lookup : C.TABLES[index]? = some (.mk_tabletype limits type) := by
      simp only [labelContext,proj_uN_0] at bound selected
      simpa only [getElem!_pos C.TABLES index bound,List.getElem?_eq_getElem bound] using congrArg some selected
    obtain ⟨address,object,mapped,found,objectType⟩ := table_lookup bindings lookup
    cases operandTypes with
    | cons valueTyped tail => cases tail with
      | cons sizeTyped tail =>
        cases tail
        obtain ⟨reference,rfl,referenceTyped⟩ := reference_operand valueTyped
        obtain ⟨delta,rfl,deltaBound⟩ := integer_val_inv (ty:=.I32) sizeTyped
        have decoded : integer .I32 (integerVal .I32 delta) = some delta := integer_accepts .I32 delta deltaBound
        refine ⟨front,reference,delta,address,object,split,mapped,found,?_⟩
        have split' : f.vals = (front++[val_ref reference])++[integerVal .I32 delta] := by
          simpa [List.append_assoc] using split
        have rawTyped : Ref_ok s reference (tableElementType object.TYPE) := by rw [objectType]; exact referenceTyped
        have indexBound : index<2^32 := by cases instructionWf; rename_i valid; cases valid; norm_num at *; omega
        have constant_admin : ∀ bits, admininstr_val (integerVal .I32 bits) = Segment.i32 bits := fun _ => rfl
        intro choice allowed
        obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf hf
        have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
        have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
        cases allowed with
        | refused =>
          have resultTyped := integer_val_typed typed.typed.store .I32 (2^32-1) (by decide)
          have freshFrame := continuation [integerVal .I32 (2^32-1)] (.cons resultTyped .nil)
          refine ⟨_,by simp only [tableGrow,split',pop_append,mapped,decoded,found,as_reference_value,advance],
            ⟨active_frame_preservation typed.typed freshFrame rfl,typed.contents⟩,extend_store_refl _ typed.typed.store,NextSim.single ?_⟩
          have source := table_grow_fail_step s f.toFrame index delta reference typed.typed.store frameWf indexBound deltaBound
          have full := mutable_stack_simulation s s ambient f rest (.TABLE_GROW (.mk_uN index)) after front [val_ref reference,integerVal .I32 delta]
            [integerVal .I32 (2^32-1)] typed.typed.ambient labelsWf frontWf tailWf restWf heights
            (by simpa [AFrame.toFrame,vals,reference_admin_value,admininstr_instr,constant_admin] using source)
          simpa only [split] using full
        | @grown grownObject grown =>
          have objectTyped := typed.contents.tables object (List.mem_of_getElem? found)
          obtain ⟨newTyped,objectExtension⟩ := growtable_typed objectTyped rawTyped grown
          obtain ⟨extension,contents⟩ := table_replacement_preserves s address object grownObject typed.typed.store typed.contents found objectExtension newTyped
          have bound : object.REFS.length < 2^32 := by
            exact table_size_bound typed.contents (List.mem_of_getElem? found)
          have resultTyped := integer_val_typed typed.typed.store .I32 (object.REFS.length) bound
          have frameNext := continuation [integerVal .I32 (object.REFS.length)] (.cons resultTyped .nil)
          have fresh := (active_frame_preservation typed.typed frameNext rfl).extend_same extension rfl
          refine ⟨_,by simp only [tableGrow,split',pop_append,mapped,decoded,found,as_reference_value,advance],⟨fresh,contents⟩,extension,NextSim.single ?_⟩
          have tableEq : fun_table ⟨s,f.toFrame⟩ (.mk_uN index) = object := by
            simp [fun_table,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
          have storeEq : {s with TABLES := s.TABLES.modify f.module.TABLES[index]! (fun _ => grownObject)} =
              {s with TABLES := s.TABLES.set address grownObject} := by
            simp [List.getElem!_eq_getElem?_getD,mapped,Option.getD_some,List.modify_eq_set_getElem?,found]
          have source := table_grow_success_step s f.toFrame index delta reference grownObject typed.typed.store frameWf indexBound deltaBound
            (List.getElem?_eq_some_iff.mp mapped).1 (by simpa only [tableEq] using bound)
            (by simpa only [tableEq] using grown) (by simpa only [AFrame.toFrame,storeEq] using (extend_store_wf extension).2)
          rw [tableEq] at source
          simp only [AFrame.toFrame,storeEq] at source
          have full := mutable_stack_simulation s {s with TABLES:=s.TABLES.set address grownObject} ambient f rest (.TABLE_GROW (.mk_uN index)) after front
            [val_ref reference,integerVal .I32 delta] [integerVal .I32 (object.REFS.length)] typed.typed.ambient labelsWf frontWf tailWf restWf heights
            (by simpa [AFrame.toFrame,vals,reference_admin_value,admininstr_instr,constant_admin] using source)
          simpa only [split] using full
end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## TableRead -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

def tableGet (s : AState) (f : AFrame) (rest : List AFrame) (index : Nat) (after : List instr) : AResult :=
  match pop f.vals, f.module.TABLES[index]? with
  | some (front,value), some address => match integer .I32 value, s.store.TABLES[address]? with
    | some position, some object =>
      if inside : position < object.REFS.length then
        advance s {f with code := after, vals := front ++ [val_ref object.REFS[position]]} rest
      else .trap
    | _,_ => .stuck
  | _,_ => .stuck

def tableSize (s : AState) (f : AFrame) (rest : List AFrame) (index : Nat) (after : List instr) : AResult :=
  match f.module.TABLES[index]? with
  | none => .stuck
  | some address => match s.store.TABLES[address]? with
    | none => .stuck
    | some object => advance s {f with code := after, vals := f.vals ++ [integerVal .I32 object.REFS.length]} rest

theorem table_get_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .TABLE_GET (.mk_uN index) :: after} :: rest,[]⟩) :
    (∃ next, tableGet ⟨s,ambient,{f with code := .TABLE_GET (.mk_uN index) :: after} :: rest,[]⟩ f rest index after = .next next ∧
      CoreTyped next ∧ NextSim ⟨s,ambient,{f with code := .TABLE_GET (.mk_uN index) :: after} :: rest,[]⟩ next) ∨
    (tableGet ⟨s,ambient,{f with code := .TABLE_GET (.mk_uN index) :: after} :: rest,[]⟩ f rest index after = .trap ∧
      ∃ count, 0 < count ∧ StepsHN count (decode ⟨s,ambient,{f with code := .TABLE_GET (.mk_uN index) :: after} :: rest,[]⟩) []
        ⟨⟨s,ambient⟩,[.TRAP]⟩) := by
  have hf : FrameTyped s {f with code := .TABLE_GET (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | table_get _ _ type limits bound selected contextWf instructionWf =>
    have lookup : C.TABLES[index]? = some (.mk_tabletype limits type) := by
      simp only [labelContext,proj_uN_0] at bound selected
      simpa only [getElem!_pos C.TABLES index bound,List.getElem?_eq_getElem bound] using congrArg some selected
    obtain ⟨address,object,mapped,found,objectType⟩ := table_lookup bindings lookup
    cases operandTypes with
    | cons valueTyped tail =>
      cases tail
      obtain ⟨position,rfl,positionBound⟩ := integer_val_inv (ty := .I32) valueTyped
      have decoded : integer .I32 (integerVal .I32 position) = some position := integer_accepts .I32 position positionBound
      obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf hf
      have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
      have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
      have indexBound : index < 2^32 := by cases instructionWf; rename_i valid; cases valid; norm_num at *; omega
      have tableEq : fun_table ⟨s,f.toFrame⟩ (.mk_uN index) = object := by
        simp [fun_table,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
      have source := Spec.table_get_step s f.toFrame index position typed.typed.store frameWf indexBound positionBound
      rw [tableEq] at source
      by_cases inside : position < object.REFS.length
      · have refTyped := table_references typed.contents (List.mem_of_getElem? found) object.REFS[position] (List.getElem_mem inside)
        rw [objectType] at refTyped
        have resultTyped : Val_ok s (val_ref object.REFS[position]) (valtype_reftype type) :=
          .reftype s _ type refTyped typed.typed.store
        have freshFrame := continuation [val_ref object.REFS[position]] (.cons resultTyped .nil)
        apply Or.inl
        refine ⟨_,by simp [tableGet,split,pop_append,mapped,decoded,found,inside,advance],
          ⟨active_frame_preservation typed.typed freshFrame rfl,typed.contents⟩,NextSim.single ?_⟩
        simp only [inside,ite_true,getElem!_pos object.REFS position inside] at source
        have converted : admininstr_val (val_ref object.REFS[position]) = admininstr_ref object.REFS[position] := by
          generalize object.REFS[position] = value
          cases value <;> rfl
        have source' : StepH ⟨⟨s,f.toFrame⟩,vals [integerVal .I32 position] ++ [admininstr_instr (.TABLE_GET (.mk_uN index))]⟩ []
            ⟨⟨s,f.toFrame⟩,vals [val_ref object.REFS[position]]⟩ := by
          simpa only [vals,List.map_cons,List.map_nil,List.singleton_append,converted,admininstr_instr,
            show admininstr_val (integerVal .I32 position) = Segment.i32 position from rfl] using source
        simpa only [split] using mutable_stack_simulation s s ambient f rest (.TABLE_GET (.mk_uN index)) after front
          [integerVal .I32 position] [val_ref object.REFS[position]] typed.typed.ambient labelsWf frontWf tailWf restWf heights source'
      · apply Or.inr
        refine ⟨by simp [tableGet,split,pop_append,mapped,decoded,found,inside],?_⟩
        simp only [inside,ite_false] at source
        have full := operand_trap_simulation s ambient f rest (.TABLE_GET (.mk_uN index)) after front
          [integerVal .I32 position] typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
          (by simpa [vals,admininstr_val,integerVal,Segment.i32,numtype_Inn,admininstr_instr] using source)
        simpa only [split] using full

theorem table_size_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .TABLE_SIZE (.mk_uN index) :: after} :: rest,[]⟩) :
    ∃ next, tableSize ⟨s,ambient,{f with code := .TABLE_SIZE (.mk_uN index) :: after} :: rest,[]⟩ f rest index after = .next next ∧
      CoreTyped next ∧ NextSim ⟨s,ambient,{f with code := .TABLE_SIZE (.mk_uN index) :: after} :: rest,[]⟩ next := by
  have hf : FrameTyped s {f with code := .TABLE_SIZE (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | table_size _ _ limits type bound selected contextWf instructionWf =>
    have lookup : C.TABLES[index]? = some (.mk_tabletype limits type) := by
      simp only [labelContext,proj_uN_0] at bound selected
      simpa only [getElem!_pos C.TABLES index bound,List.getElem?_eq_getElem bound] using congrArg some selected
    obtain ⟨address,object,mapped,found,objectType⟩ := table_lookup bindings lookup
    cases operandTypes
    have sizeBound := table_size_bound typed.contents (List.mem_of_getElem? found)
    have resultTyped := integer_val_typed typed.typed.store .I32 object.REFS.length sizeBound
    have freshFrame := continuation [integerVal .I32 object.REFS.length] (.cons resultTyped .nil)
    have actualFrame : FrameTyped s {f with code := after,vals := f.vals ++ [integerVal .I32 object.REFS.length]} [] := by
      simpa only [split,List.append_nil] using freshFrame
    refine ⟨_,by simp only [tableSize,mapped,found,advance],
      ⟨active_frame_preservation typed.typed actualFrame rfl,typed.contents⟩,NextSim.single ?_⟩
    obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf hf
    have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
    have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
    have indexBound : index < 2^32 := by cases instructionWf; rename_i valid; cases valid; norm_num at *; omega
    have tableEq : fun_table ⟨s,f.toFrame⟩ (.mk_uN index) = object := by
      simp [fun_table,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
    have source := Spec.table_size_step s f.toFrame index typed.typed.store frameWf indexBound (by simpa only [tableEq] using sizeBound)
    rw [tableEq] at source
    have height : ∀ label ∈ f.labels, label.height ≤ f.vals.length := by simpa only [split,List.append_nil] using heights
    have full := mutable_stack_simulation s s ambient f rest (.TABLE_SIZE (.mk_uN index)) after f.vals []
      [integerVal .I32 object.REFS.length] typed.typed.ambient labelsWf valuesWf tailWf restWf height
      (by simpa [vals,admininstr_val,integerVal,Segment.i32,numtype_Inn,admininstr_instr] using source)
    simpa only [List.append_nil] using full

end Itasca.Runtime.SourceMachine.Stateful

end
