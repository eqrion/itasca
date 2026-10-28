import Exec.Spec.Context
import Mathlib.Data.List.Forall2
import Mathlib.Tactic
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
