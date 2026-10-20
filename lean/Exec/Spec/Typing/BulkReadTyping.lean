import Exec.Spec.Typing.FramePayloadTyping
import Exec.Spec.Typing.NumericReadTyping

/-! Zero-length bulk reads and recursive fill/copy/memory-init expansions
preserve semantic typing. Both copy directions use the same typed program shape. -/

namespace Exec.Spec
open SpecExt

theorem source_instr_wf_of_admin {instruction : instr} (typed : wf_admininstr (admininstr_instr instruction)) :
    wf_instr instruction := by
  cases instruction <;> cases typed <;> constructor <;> assumption

def BulkInstruction : admininstr → Bool
  | .TABLE_FILL _ | .TABLE_COPY _ _ | .TABLE_INIT _ _
    | .MEMORY_FILL | .MEMORY_COPY | .MEMORY_INIT _ => true
  | _ => false

theorem bulk_instruction_effect {s : store} {context : _root_.context} {instruction : admininstr}
    {input output : List valtype}
    (typed : Instr_ok2 s context instruction (.mk_functype (.mk_list input) (.mk_list output)))
    (bulk : BulkInstruction instruction=true) : input.length=3 ∧ output=[] := by
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    cases primitive <;> simp_all [admininstr_instr,BulkInstruction]
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref,BulkInstruction] at bulk
  all_goals simp [BulkInstruction] at bulk

theorem bulk_zero_typing_preserved {s : store} {context : _root_.context} {args : List val} {op : admininstr}
    {input output : List valtype} (arity : args.length=3) (bulk : BulkInstruction op=true)
    (typed : Instrs_ok2 s context (vals args++[op]) (.mk_functype (.mk_list input) (.mk_list output))) :
    Instrs_ok2 s context [] (.mk_functype (.mk_list input) (.mk_list output)) := by
  have wf := instrs_ok2_wf typed
  apply value_operation_at_context typed
  intro params results primitive
  obtain ⟨count,rfl⟩ := bulk_instruction_effect primitive bulk
  exact ⟨count.trans arity.symm,fun _ => instrs_identity wf.1 wf.2.1 []⟩

set_option maxHeartbeats 1600000 in
theorem read_zero_typing_preserved {s : store} {context : _root_.context} {before : config}
    (source : Step_read before []) {input output : List valtype}
    (typed : Instrs_ok2 s context (configurationInstructions before) (.mk_functype (.mk_list input) (.mk_list output))) :
    Instrs_ok2 s context [] (.mk_functype (.mk_list input) (.mk_list output)) := by
  cases source
  all_goals first
    | change Instrs_ok2 s context (vals [.CONST _ _,.CONST _ _,.CONST _ _]++[_]) _ at typed
    | change Instrs_ok2 s context (vals [.CONST _ _,_,.CONST _ _]++[_]) _ at typed
  all_goals exact bulk_zero_typing_preserved rfl rfl typed

theorem source_instruction_stack {s : store} (storeWf : wf_store s) {context : _root_.context}
    {instruction : instr} {params results : List valtype}
    (operator : Instr_ok context instruction (.mk_functype (.mk_list params) (.mk_list results))) :
    Instrs_ok2 s context [admininstr_instr instruction] (.mk_functype (.mk_list params) (.mk_list results)) := by
  have contextWf : wf_context context := by cases operator <;> assumption
  have instructionWf : wf_instr instruction := by cases operator <;> assumption
  exact .instr _ _ _ _ _ (.plain _ _ _ _ _ operator storeWf contextWf instructionWf)
    storeWf contextWf (wf_admininstr_instr instructionWf)

theorem instruction_on_values {s : store} (storeWf : wf_store s) {context : _root_.context}
    {instruction : instr} {params results : List valtype} {values : List val}
    (operator : Instr_ok context instruction (.mk_functype (.mk_list params) (.mk_list results)))
    (arguments : ResultsTyped s params values) :
    Instrs_ok2 s context (vals values++[admininstr_instr instruction])
      (.mk_functype (.mk_list []) (.mk_list results)) := by
  have contextWf : wf_context context := by cases operator <;> assumption
  have instructionWf : wf_instr instruction := by cases operator <;> assumption
  have typed := Instrs_ok2.instr s context (admininstr_instr instruction) params results
    (.plain _ _ _ _ _ operator storeWf contextWf instructionWf) storeWf contextWf (wf_admininstr_instr instructionWf)
  exact instrs_sequence (values_instrs_ok storeWf contextWf arguments) typed

theorem table_fill_success_typing_preserved {s : store} {context : _root_.context}
    (position next count nextCount : num_) (value : val) (index : idx)
    (setWf : wf_admininstr (.TABLE_SET index))
    (nextWf : wf_admininstr (.CONST .I32 next)) (nextCountWf : wf_admininstr (.CONST .I32 nextCount))
    {input output : List valtype}
    (typed : Instrs_ok2 s context [.CONST .I32 position,admininstr_val value,.CONST .I32 count,.TABLE_FILL index]
      (.mk_functype (.mk_list input) (.mk_list output))) :
    Instrs_ok2 s context [.CONST .I32 position,admininstr_val value,.TABLE_SET index,
      .CONST .I32 next,admininstr_val value,.CONST .I32 nextCount,.TABLE_FILL index]
      (.mk_functype (.mk_list input) (.mk_list output)) := by
  change Instrs_ok2 s context (vals [.CONST .I32 position,value,.CONST .I32 count]++[.TABLE_FILL index]) _ at typed
  apply value_operation_at_context typed
  intro params results primitive
  generalize same : admininstr.TABLE_FILL index=instruction at primitive
  have storeWf : wf_store s := by cases primitive <;> assumption
  have contextWf : wf_context context := by cases primitive <;> assumption
  cases primitive
  case plain =>
    rename_i source _ _ _ sourceTyped
    cases source <;> simp [admininstr_instr] at same
    cases same
    have originalFill := sourceTyped
    cases sourceTyped
    rename_i type limits _ _ _ _ _
    have setSourceWf := source_instr_wf_of_admin (instruction := .TABLE_SET index) setWf
    have setTyped : Instr_ok context (.TABLE_SET index)
        (.mk_functype (.mk_list [.I32,valtype_reftype type]) (.mk_list [])) := by
      apply Instr_ok.table_set <;> assumption
    refine ⟨rfl,?_⟩
    intro arguments
    cases arguments with
    | cons positionTyped rest =>
      cases rest with
      | cons valueTyped rest =>
        have first := instruction_on_values storeWf setTyped (.cons positionTyped (.cons valueTyped .nil))
        have nextTyped := Val_ok.numtype s .I32 next storeWf (val_wf_of_admin nextWf)
        have countTyped := Val_ok.numtype s .I32 nextCount storeWf (val_wf_of_admin nextCountWf)
        have second := instruction_on_values storeWf originalFill (.cons nextTyped (.cons valueTyped (.cons countTyped .nil)))
        simpa only [vals,List.map_cons,List.map_nil,admininstr_val,admininstr_instr,List.append_assoc,List.cons_append,List.nil_append]
          using instrs_sequence first second
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

theorem memory_fill_success_typing_preserved {s : store} {context : _root_.context}
    (position next count nextCount : num_) (value : val) (memoryArgument : memarg) (zeroArgument : fun_memarg0 memoryArgument)
    (setWf : wf_admininstr (.STORE .I32 (some (.mk_sz 8)) memoryArgument))
    (nextWf : wf_admininstr (.CONST .I32 next)) (nextCountWf : wf_admininstr (.CONST .I32 nextCount))
    {input output : List valtype}
    (typed : Instrs_ok2 s context [.CONST .I32 position,admininstr_val value,.CONST .I32 count,.MEMORY_FILL]
      (.mk_functype (.mk_list input) (.mk_list output))) :
    Instrs_ok2 s context [.CONST .I32 position,admininstr_val value,.STORE .I32 (some (.mk_sz 8)) memoryArgument,
      .CONST .I32 next,admininstr_val value,.CONST .I32 nextCount,.MEMORY_FILL]
      (.mk_functype (.mk_list input) (.mk_list output)) := by
  change Instrs_ok2 s context (vals [.CONST .I32 position,value,.CONST .I32 count]++[.MEMORY_FILL]) _ at typed
  apply value_operation_at_context typed
  intro params results primitive
  generalize same : admininstr.MEMORY_FILL=instruction at primitive
  have storeWf : wf_store s := by cases primitive <;> assumption
  have contextWf : wf_context context := by cases primitive <;> assumption
  cases primitive
  case plain =>
    rename_i source _ _ _ sourceTyped
    cases source <;> simp [admininstr_instr] at same
    cases same
    have originalFill := sourceTyped
    cases sourceTyped
    rename_i memoryType _ _ _ _ _
    have setSourceWf := source_instr_wf_of_admin (instruction := .STORE .I32 (some (.mk_sz 8)) memoryArgument) setWf
    have setTyped : Instr_ok context (.STORE .I32 (some (.mk_sz 8)) memoryArgument)
        (.mk_functype (.mk_list [.I32,.I32]) (.mk_list [])) := by
      apply Instr_ok.store_pack (v_Inn := .I32) (v_M := 8) (mt := memoryType)
      all_goals first
        | assumption
        | (cases zeroArgument; norm_num [proj_uN_0])
    refine ⟨rfl,?_⟩
    intro arguments
    cases arguments with
    | cons positionTyped rest =>
      cases rest with
      | cons valueTyped rest =>
        have first := instruction_on_values storeWf setTyped (.cons positionTyped (.cons valueTyped .nil))
        have nextTyped := Val_ok.numtype s .I32 next storeWf (val_wf_of_admin nextWf)
        have countTyped := Val_ok.numtype s .I32 nextCount storeWf (val_wf_of_admin nextCountWf)
        have second := instruction_on_values storeWf originalFill (.cons nextTyped (.cons valueTyped (.cons countTyped .nil)))
        simpa only [vals,List.map_cons,List.map_nil,admininstr_val,admininstr_instr,List.append_assoc,List.cons_append,List.nil_append]
          using instrs_sequence first second
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

theorem table_copy_success_typing_preserved {s : store} {context : _root_.context}
    (destination source count writeDestination readSource nextDestination nextSource nextCount : num_)
    (destinationIndex sourceIndex : idx)
    (getWf : wf_admininstr (.TABLE_GET sourceIndex)) (setWf : wf_admininstr (.TABLE_SET destinationIndex))
    (writeWf : wf_admininstr (.CONST .I32 writeDestination)) (readWf : wf_admininstr (.CONST .I32 readSource))
    (nextDestinationWf : wf_admininstr (.CONST .I32 nextDestination)) (nextSourceWf : wf_admininstr (.CONST .I32 nextSource))
    (nextCountWf : wf_admininstr (.CONST .I32 nextCount)) {input output : List valtype}
    (typed : Instrs_ok2 s context [.CONST .I32 destination,.CONST .I32 source,.CONST .I32 count,.TABLE_COPY destinationIndex sourceIndex]
      (.mk_functype (.mk_list input) (.mk_list output))) :
    Instrs_ok2 s context [.CONST .I32 writeDestination,.CONST .I32 readSource,.TABLE_GET sourceIndex,.TABLE_SET destinationIndex,
      .CONST .I32 nextDestination,.CONST .I32 nextSource,.CONST .I32 nextCount,.TABLE_COPY destinationIndex sourceIndex]
      (.mk_functype (.mk_list input) (.mk_list output)) := by
  change Instrs_ok2 s context (vals [.CONST .I32 destination,.CONST .I32 source,.CONST .I32 count]++[.TABLE_COPY destinationIndex sourceIndex]) _ at typed
  apply value_operation_at_context typed
  intro params results primitive
  generalize same : admininstr.TABLE_COPY destinationIndex sourceIndex=instruction at primitive
  have storeWf : wf_store s := by cases primitive <;> assumption
  have contextWf : wf_context context := by cases primitive <;> assumption
  cases primitive
  case plain =>
    rename_i operator _ _ _ operatorTyped
    cases operator <;> simp [admininstr_instr] at same
    rcases same with ⟨destinationEq,sourceEq⟩
    cases destinationEq
    cases sourceEq
    have originalCopy := operatorTyped
    cases operatorTyped
    rename_i destinationLimits type sourceLimits _ _ _ _ _ _ _ _
    have getSourceWf := source_instr_wf_of_admin (instruction := .TABLE_GET sourceIndex) getWf
    have setSourceWf := source_instr_wf_of_admin (instruction := .TABLE_SET destinationIndex) setWf
    have loadTyped : Instr_ok context (.TABLE_GET sourceIndex)
        (.mk_functype (.mk_list [.I32]) (.mk_list [valtype_reftype type])) := by
      apply Instr_ok.table_get <;> assumption
    have storeTyped : Instr_ok context (.TABLE_SET destinationIndex)
        (.mk_functype (.mk_list [.I32,valtype_reftype type]) (.mk_list [])) := by
      apply Instr_ok.table_set <;> assumption
    refine ⟨rfl,fun _ => ?_⟩
    have writeValue := Val_ok.numtype s .I32 writeDestination storeWf (val_wf_of_admin writeWf)
    have readValue := Val_ok.numtype s .I32 readSource storeWf (val_wf_of_admin readWf)
    have arguments := values_instrs_ok storeWf contextWf (.cons writeValue (.cons readValue .nil))
    have loaded := instrs_sequence arguments (instrs_frame (source_instruction_stack storeWf loadTyped) [.I32])
    have stored := instrs_sequence loaded (source_instruction_stack storeWf storeTyped)
    have destValue := Val_ok.numtype s .I32 nextDestination storeWf (val_wf_of_admin nextDestinationWf)
    have sourceValue := Val_ok.numtype s .I32 nextSource storeWf (val_wf_of_admin nextSourceWf)
    have countValue := Val_ok.numtype s .I32 nextCount storeWf (val_wf_of_admin nextCountWf)
    have recur := instruction_on_values storeWf originalCopy (.cons destValue (.cons sourceValue (.cons countValue .nil)))
    simpa only [vals,List.map_cons,List.map_nil,admininstr_val,admininstr_instr,List.append_assoc,List.cons_append,List.nil_append]
      using instrs_sequence stored recur
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

def bulkByteLoad (argument : memarg) : instr :=
  .LOAD .I32 (some (.mk_loadop__0 .I32 (.mk_loadop_Inn (.mk_sz 8) .U))) argument

def bulkByteStore (argument : memarg) : instr := .STORE .I32 (some (.mk_sz 8)) argument

theorem memory_copy_success_typing_preserved {s : store} {context : _root_.context}
    (destination source count writeDestination readSource nextDestination nextSource nextCount : num_)
    (memoryArgument : memarg) (zeroArgument : fun_memarg0 memoryArgument)
    (getWf : wf_admininstr (admininstr_instr (bulkByteLoad memoryArgument))) (setWf : wf_admininstr (admininstr_instr (bulkByteStore memoryArgument)))
    (writeWf : wf_admininstr (.CONST .I32 writeDestination)) (readWf : wf_admininstr (.CONST .I32 readSource))
    (nextDestinationWf : wf_admininstr (.CONST .I32 nextDestination)) (nextSourceWf : wf_admininstr (.CONST .I32 nextSource))
    (nextCountWf : wf_admininstr (.CONST .I32 nextCount)) {input output : List valtype}
    (typed : Instrs_ok2 s context [.CONST .I32 destination,.CONST .I32 source,.CONST .I32 count,.MEMORY_COPY]
      (.mk_functype (.mk_list input) (.mk_list output))) :
    Instrs_ok2 s context [.CONST .I32 writeDestination,.CONST .I32 readSource,admininstr_instr (bulkByteLoad memoryArgument),admininstr_instr (bulkByteStore memoryArgument),
      .CONST .I32 nextDestination,.CONST .I32 nextSource,.CONST .I32 nextCount,.MEMORY_COPY]
      (.mk_functype (.mk_list input) (.mk_list output)) := by
  change Instrs_ok2 s context (vals [.CONST .I32 destination,.CONST .I32 source,.CONST .I32 count]++[.MEMORY_COPY]) _ at typed
  apply value_operation_at_context typed
  intro params results primitive
  generalize same : admininstr.MEMORY_COPY=instruction at primitive
  have storeWf : wf_store s := by cases primitive <;> assumption
  have contextWf : wf_context context := by cases primitive <;> assumption
  cases primitive
  case plain =>
    rename_i operator _ _ _ operatorTyped
    cases operator <;> simp [admininstr_instr] at same
    cases same
    have originalCopy := operatorTyped
    cases operatorTyped
    rename_i memoryType _ _ _ _ _
    have getSourceWf := source_instr_wf_of_admin (instruction := bulkByteLoad memoryArgument) getWf
    have setSourceWf := source_instr_wf_of_admin (instruction := bulkByteStore memoryArgument) setWf
    have loadTyped : Instr_ok context (bulkByteLoad memoryArgument)
        (.mk_functype (.mk_list [.I32]) (.mk_list [.I32])) := by
      apply Instr_ok.load_pack (v_Inn := .I32) (v_M := 8) (v_sx := .U) (mt := memoryType)
      all_goals first | assumption | (cases zeroArgument; norm_num [proj_uN_0])
    have storeTyped : Instr_ok context (bulkByteStore memoryArgument)
        (.mk_functype (.mk_list [.I32,.I32]) (.mk_list [])) := by
      apply Instr_ok.store_pack (v_Inn := .I32) (v_M := 8) (mt := memoryType)
      all_goals first | assumption | (cases zeroArgument; norm_num [proj_uN_0])
    refine ⟨rfl,fun _ => ?_⟩
    have writeValue := Val_ok.numtype s .I32 writeDestination storeWf (val_wf_of_admin writeWf)
    have readValue := Val_ok.numtype s .I32 readSource storeWf (val_wf_of_admin readWf)
    have arguments := values_instrs_ok storeWf contextWf (.cons writeValue (.cons readValue .nil))
    have loaded := instrs_sequence arguments (instrs_frame (source_instruction_stack storeWf loadTyped) [.I32])
    have stored := instrs_sequence loaded (source_instruction_stack storeWf storeTyped)
    have destValue := Val_ok.numtype s .I32 nextDestination storeWf (val_wf_of_admin nextDestinationWf)
    have sourceValue := Val_ok.numtype s .I32 nextSource storeWf (val_wf_of_admin nextSourceWf)
    have countValue := Val_ok.numtype s .I32 nextCount storeWf (val_wf_of_admin nextCountWf)
    have recur := instruction_on_values storeWf originalCopy (.cons destValue (.cons sourceValue (.cons countValue .nil)))
    simpa only [bulkByteLoad,bulkByteStore,vals,List.map_cons,List.map_nil,admininstr_val,admininstr_instr,List.append_assoc,List.cons_append,List.nil_append]
      using instrs_sequence stored recur
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

theorem memory_init_success_typing_preserved {s : store} {context : _root_.context}
    (destination source count writeDestination readSource nextDestination nextSource nextCount : num_)
    (dataIndex : idx) (memoryArgument : memarg) (zeroArgument : fun_memarg0 memoryArgument)
    (setWf : wf_admininstr (admininstr_instr (bulkByteStore memoryArgument)))
    (writeWf : wf_admininstr (.CONST .I32 writeDestination)) (readWf : wf_admininstr (.CONST .I32 readSource))
    (nextDestinationWf : wf_admininstr (.CONST .I32 nextDestination)) (nextSourceWf : wf_admininstr (.CONST .I32 nextSource))
    (nextCountWf : wf_admininstr (.CONST .I32 nextCount)) {input output : List valtype}
    (typed : Instrs_ok2 s context [.CONST .I32 destination,.CONST .I32 source,.CONST .I32 count,.MEMORY_INIT dataIndex]
      (.mk_functype (.mk_list input) (.mk_list output))) :
    Instrs_ok2 s context [.CONST .I32 writeDestination,.CONST .I32 readSource,admininstr_instr (bulkByteStore memoryArgument),
      .CONST .I32 nextDestination,.CONST .I32 nextSource,.CONST .I32 nextCount,.MEMORY_INIT dataIndex]
      (.mk_functype (.mk_list input) (.mk_list output)) := by
  change Instrs_ok2 s context (vals [.CONST .I32 destination,.CONST .I32 source,.CONST .I32 count]++[.MEMORY_INIT dataIndex]) _ at typed
  apply value_operation_at_context typed
  intro params results primitive
  generalize same : admininstr.MEMORY_INIT dataIndex=instruction at primitive
  have storeWf : wf_store s := by cases primitive <;> assumption
  have contextWf : wf_context context := by cases primitive <;> assumption
  cases primitive
  case plain =>
    rename_i operator _ _ _ operatorTyped
    cases operator <;> simp [admininstr_instr] at same
    cases same
    have originalCopy := operatorTyped
    cases operatorTyped
    rename_i memoryType _ _ _ _ _ _ _
    have setSourceWf := source_instr_wf_of_admin (instruction := bulkByteStore memoryArgument) setWf
    have storeTyped : Instr_ok context (bulkByteStore memoryArgument)
        (.mk_functype (.mk_list [.I32,.I32]) (.mk_list [])) := by
      apply Instr_ok.store_pack (v_Inn := .I32) (v_M := 8) (mt := memoryType)
      all_goals first | assumption | (cases zeroArgument; norm_num [proj_uN_0])
    refine ⟨rfl,fun _ => ?_⟩
    have writeValue := Val_ok.numtype s .I32 writeDestination storeWf (val_wf_of_admin writeWf)
    have readValue := Val_ok.numtype s .I32 readSource storeWf (val_wf_of_admin readWf)
    have arguments := values_instrs_ok storeWf contextWf (.cons writeValue (.cons readValue .nil))
    have stored := instrs_sequence arguments (source_instruction_stack storeWf storeTyped)
    have destValue := Val_ok.numtype s .I32 nextDestination storeWf (val_wf_of_admin nextDestinationWf)
    have sourceValue := Val_ok.numtype s .I32 nextSource storeWf (val_wf_of_admin nextSourceWf)
    have countValue := Val_ok.numtype s .I32 nextCount storeWf (val_wf_of_admin nextCountWf)
    have recur := instruction_on_values storeWf originalCopy (.cons destValue (.cons sourceValue (.cons countValue .nil)))
    simpa only [bulkByteLoad,bulkByteStore,vals,List.map_cons,List.map_nil,admininstr_val,admininstr_instr,List.append_assoc,List.cons_append,List.nil_append]
      using instrs_sequence stored recur
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

end Exec.Spec
