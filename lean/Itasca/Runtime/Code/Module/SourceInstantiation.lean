import Itasca.Runtime.Spec.Instantiation
import Itasca.Runtime.Spec.SegmentPrograms
import Itasca.Runtime.Code.Local.Source.SourceSegmentPrograms
import Itasca.Runtime.Code.Module.SegmentPayloadBounds
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

private theorem mapped_two {α β γ δ : Type} (xs : List α) (f : α → β) (g : α → γ)
    (h : β → γ → δ) : Map₂ h (xs.map f) (xs.map g) = xs.map (fun x => h (f x) (g x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [Map₂, List.map_cons, List.ap, List.zipWith_cons_cons] using congrArg (h (f x) (g x) :: ·) ih

private theorem mapped_three {α β γ δ ε : Type} (xs : List α) (f : α → β) (g : α → γ)
    (h : α → δ) (combine : β → γ → δ → ε) :
    Map₃ combine (xs.map f) (xs.map g) (xs.map h) = xs.map (fun x => combine (f x) (g x) (h x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [Map₃, List.map_cons, List.ap, List.zipWith_cons_cons] using congrArg (combine (f x) (g x) (h x) :: ·) ih

private theorem forall_three {α β γ δ : Type} (xs : List α) (f : α → β) (g : α → γ) (h : α → δ)
    (P : β → γ → δ → Prop) (checked : ∀ x ∈ xs, P (f x) (g x) (h x)) :
    Forall₃ P (xs.map f) (xs.map g) (xs.map h) := by
  induction xs with
  | nil => simp [Forall₃]
  | cons x xs ih =>
    have head := checked x (by simp)
    have tail := ih (fun a mem => checked a (by simp [mem]))
    simpa [Forall₃] using And.intro head tail

private theorem padded_count {α : Type} {R : α → List U8 → Prop} {id values bytes}
    (encoded : ModuleBinary.PaddedEncoding id (ModuleBinary.VecEncoding R) [] values bytes) :
    values.length < 2^32 := by
  obtain ⟨customs, sec, _, secProof, _⟩ := encoded
  cases secProof with
  | absent => simp
  | present content =>
    obtain ⟨size, payload, _, ⟨count, entries, bounded, _, _⟩, _⟩ := content
    exact bounded.value_lt

theorem module_segment_counts {R raw bytes profile}
    (encoded : ModuleBinary.ModuleEncodingWith R raw bytes profile) :
    raw.elements.length < 2^32 ∧ raw.data.length < 2^32 := by
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
    codes, datas, customs, _, _, _, _, _, _, _, _, hel, _, _, hd, _, _, _, _⟩ := encoded
  exact ⟨padded_count hel, padded_count hd⟩

private theorem evaluation_value_wf {before after : state} {expression : expr} {value : val}
    (evaluated : Eval_expr before expression after [value]) : wf_val value := by
  cases evaluated with
  | mk_Eval_expr _ _ final =>
    have valueSyntax := (Spec.wf_config_parts final).2 (admininstr_val value) (by simp [Map])
    cases value <;> simp only [admininstr_val] at valueSyntax <;> cases valueSyntax <;> constructor <;> assumption

private theorem evaluated_values_wf {α : Type} {originals : List α} {values : List val}
    {before after : state} {expression : α → expr}
    (evaluated : List.Forall₂ (fun original value => Eval_expr before (expression original) after [value]) originals values) :
    Forall wf_val values := by
  induction evaluated with
  | nil => simp [Forall]
  | cons first rest ih =>
    intro value present
    rcases List.mem_cons.mp present with rfl | present
    · exact evaluation_value_wf first
    · exact ih value present

/-- Canonical raw module syntax discharges the generated instantiation rule's
structural side conditions. Allocation and initializer evaluations are concrete
source judgments supplied by the corresponding implementation bridges. -/
theorem source_instantiate {raw : ModuleBinary.Module} {R bytes profile}
    (encoded : ModuleBinary.ModuleEncodingWith R raw bytes profile)
    (elaborates : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (typed : Module_ok (ModuleElaboration.moduleOf raw))
    (s after : store) (externals : List externaddr) (inst initialModule : moduleinst)
    (importedFunctions importedGlobals : List Nat) (values : List val) (references : List (List ref))
    (importFunctions : fun_funcs externals importedFunctions) (importGlobals : fun_globals externals importedGlobals)
    (initialEq : initialModule = ⟨raw.types.map EnvTranslation.funcType,
      importedFunctions ++ (List.range (List.zipWith CodeEntry.function raw.functions raw.codes).length).map (fun index => s.FUNCS.length + index),
      importedGlobals, [], [], [], [], []⟩)
    (globalEval : List.Forall₂ (fun original value => Eval_expr ⟨s, ⟨[], initialModule⟩⟩
      (ModuleConstants.expression original.init) ⟨s, ⟨[], initialModule⟩⟩ [value]) raw.globals values)
    (elementEval : List.Forall₂ (fun original values => List.Forall₂ (fun expression value =>
      Eval_expr ⟨s, ⟨[], initialModule⟩⟩ (ModuleConstants.expression expression)
        ⟨s, ⟨[], initialModule⟩⟩ [val_ref value]) original.init values) raw.elements references)
    (allocated : fun_allocmodule s (ModuleElaboration.moduleOf raw) externals values references (after, inst))
    (storeWf : wf_store s) :
    fun_instantiate s (ModuleElaboration.moduleOf raw) externals
      ⟨⟨after, ⟨[], inst⟩⟩,
        (Spec.Segment.elementPrograms (raw.elements.map ModuleElaboration.element)).flatten.map admininstr_instr ++
        ((Spec.Segment.dataPrograms (raw.data.map ModuleData.translate)).flatten.map admininstr_instr ++
          (raw.start.map (fun index => admininstr.CALL (.mk_uN index.val))).toList)⟩ := by
  have single : ∀ data ∈ raw.data, Spec.Segment.singleMemoryData (ModuleData.translate data) := by
    intro data member
    exact source_datas_single_memory raw elaborates typed _ (List.mem_map.mpr ⟨data, member, rfl⟩)
  have afterWf : wf_store after := by cases allocated; assumption
  have instanceWf : wf_moduleinst inst := by cases allocated; assumption
  have valuesWf := evaluated_values_wf globalEval
  have initialWf : wf_moduleinst initialModule := by
    rw [initialEq]
    constructor
    simp [Forall]
  have sourceWf : wf_module (ModuleElaboration.moduleOf raw) := by cases typed; assumption
  have globalsWf : Forall wf_global (raw.globals.map ModuleConstants.global) := by cases sourceWf; assumption
  have elementsWf : Forall wf_elem (raw.elements.map ModuleElaboration.element) := by cases sourceWf; assumption
  have datasWf : Forall wf_data (raw.data.map ModuleData.translate) := by cases sourceWf; assumption
  have startWf : Forall (fun index => wf_start (.START index)) (raw.start.map (fun index => uN.mk_uN index.val)).toList := by
    have h : Forall wf_start (raw.start.map ModuleElaboration.start).toList := by cases sourceWf; assumption
    cases hs : raw.start <;> simpa [Forall, ModuleElaboration.start, hs] using h
  have counts := module_segment_counts encoded
  have payloads := module_segment_payload_bounds encoded
  obtain ⟨runElements, programsE⟩ := Spec.Segment.element_programs (raw.elements.map ModuleElaboration.element)
    (by simpa using Nat.le_of_lt counts.1) (by
      intro segment mem
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp mem
      exact ⟨elementsWf _ (List.mem_map.mpr ⟨original,present,rfl⟩), by
        simpa [Spec.Segment.elementSize, ModuleElaboration.element] using payloads.1 original present⟩)
  obtain ⟨runDatas, programsD⟩ := Spec.Segment.data_programs (raw.data.map ModuleData.translate)
    (by simpa using Nat.le_of_lt counts.2) (by
      intro segment mem
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp mem
      exact ⟨datasWf _ (List.mem_map.mpr ⟨original,present,rfl⟩), by
        simpa [Spec.Segment.dataSize, ModuleData.translate] using payloads.2 original present, single original present⟩)
  have globalRun : List.Forall₂ (fun expression value => Eval_expr ⟨s, ⟨[], initialModule⟩⟩ expression
      ⟨s, ⟨[], initialModule⟩⟩ [value]) (raw.globals.map (fun original => ModuleConstants.expression original.init)) values :=
    List.forall₂_map_left_iff.mpr globalEval
  have elementRun : List.Forall₂ (fun expressions values => List.Forall₂ (fun expression value =>
      Eval_expr ⟨s, ⟨[], initialModule⟩⟩ expression ⟨s, ⟨[], initialModule⟩⟩ [val_ref value]) expressions values)
      (raw.elements.map (fun original => original.init.map ModuleConstants.expression)) references := by
    apply List.forall₂_map_left_iff.mpr
    exact elementEval.imp (fun _ _ h => List.forall₂_map_left_iff.mpr h)
  have startIndexWf : Forall (wf_uN 32) (raw.start.map (fun index => uN.mk_uN index.val)).toList := by
    intro index mem
    have h := startWf index mem
    cases h; assumption
  have desired : fun_instantiate s (ModuleElaboration.moduleOf raw) externals
      ⟨⟨after, ⟨[], inst⟩⟩,
        (Spec.Segment.elementPrograms (raw.elements.map ModuleElaboration.element)).flatten.map admininstr_instr ++
        ((Spec.Segment.dataPrograms (raw.data.map ModuleData.translate)).flatten.map admininstr_instr ++
          ((raw.start.map (fun index => uN.mk_uN index.val)).map admininstr.CALL).toList)⟩ := by
    apply Spec.instantiate_source (initialModule := initialModule) s after (ModuleElaboration.moduleOf raw) externals
      (raw.types.map EnvTranslation.funcType) (raw.imports.map (ModuleElaboration.importDecl raw.types))
      (List.zipWith CodeEntry.function raw.functions raw.codes) (raw.globals.map ModuleConstants.global)
      (raw.tables.map ModuleElaboration.table) (raw.memories.map ModuleElaboration.memory)
      (raw.elements.map ModuleElaboration.element) (raw.data.map ModuleData.translate)
      (raw.start.map (fun index => .mk_uN index.val)) (raw.exports.map ModuleElaboration.exportDecl)
      (raw.globals.map (fun original => ModuleConstants.expression original.init))
      (raw.globals.map (fun original => Translate.globalType original.gtype))
      (raw.elements.map (fun original => ModuleSegments.elementMode original.mode))
      (raw.elements.map (fun original => original.init.map ModuleConstants.expression))
      (raw.elements.map (fun original => Translate.referenceType original.elem)) values references importedFunctions importedGlobals inst
      (Spec.Segment.elementPrograms (raw.elements.map ModuleElaboration.element))
      (Spec.Segment.dataPrograms (raw.data.map ModuleData.translate))
    · simp only [ModuleElaboration.moduleOf, List.map_map, Option.map_map, Function.comp_def]
      rfl
    · rw [mapped_two]; rfl
    · rw [mapped_three]; rfl
    · exact importFunctions
    · exact importGlobals
    · exact initialEq
    · simpa using globalRun.length_eq
    · exact fun _ mem => List.forall₂_zip globalRun mem
    · simpa using elementRun.length_eq
    · exact fun _ mem => (List.forall₂_zip elementRun mem).length_eq
    · exact fun _ mem => fun _ member => List.forall₂_zip (List.forall₂_zip elementRun mem) member
    · exact allocated
    · exact runElements
    · exact runDatas
    · exact valuesWf
    · exact afterWf
    · exact instanceWf
    · exact programsE
    · exact programsD
    · exact Spec.Segment.initialization_config_wf _ _ _ _ _ afterWf instanceWf programsE programsD startIndexWf
    · exact sourceWf
    · simp
    · have h : List.Forall₂ (fun expression ty => wf_global (.GLOBAL ty expression))
          (raw.globals.map (fun original => ModuleConstants.expression original.init))
          (raw.globals.map (fun original => Translate.globalType original.gtype)) := by
        apply List.forall₂_map_left_iff.mpr
        apply List.forall₂_map_right_iff.mpr
        exact List.forall₂_same.mpr (fun original mem => globalsWf _ (List.mem_map.mpr ⟨original,mem,rfl⟩))
      exact fun _ mem => List.forall₂_zip h mem
    · simp
    · simp
    · apply forall_three
      intro original mem
      exact elementsWf _ (List.mem_map.mpr ⟨original,mem,rfl⟩)
    · exact startWf
    · exact initialWf
    · exact storeWf
    · simpa using Nat.le_of_lt counts.1
    · simpa using Nat.le_of_lt counts.2
  simpa only [Option.map_map, Function.comp_def] using desired
end Itasca.Runtime.Code
