import Itasca.Runtime.Compiler.Local.Callbacks.CallbackEquations
import Itasca.Runtime.Compiler.Module.SegmentSource
import Itasca.Runtime.Spec.ModuleMembership
import Itasca.Runtime.Compiler.Local.Source.SourceSegmentPrograms

/-!
Sections, each formerly its own module: CompileCache, SegmentPayloadBounds, SourceInstantiation, CompileDataCount.
-/

/-! ## CompileCache -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Canonical accepted environment parsing establishes the exact imported and
defined index-space caches retained by the executable module. -/
theorem CompileWitness.cache_input {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness allocator bytes limits executable) :
    ∃ tables memories, ModuleEnv.Cache w.env tables memories := by
  obtain ⟨run⟩ := stream.validate_streaming.accepted
    runtime.compiler.CompileSource.Insts.ItascaStreamSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator)
    0#u64 {bytes, code_start := w.codeStart, code_end := w.codeEnd}
    (initialScheduler A limits w.codeStart) w.scheduler w.initialEnv w.env w.validated
  have decoded := metadata.validate_env_with.accepted_erase
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator).metadataModuleVisitorInst
    run.environment run.region w.env run.environmentLength run.decoded run.decode_environment
  have semantic := metadata.validate_env.profile_semantic_spec run.environment
  rw [decoded, WP.spec_ok] at semantic
  obtain ⟨decls, represented, _, _, _, _⟩ := semantic
  exact ⟨decls.tables, decls.memories, represented.cache⟩

theorem CompileWitness.cache {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness allocator bytes limits executable)
    (law : Platform.AllocCorrect allocator) :
    ∃ tables memories, ModuleEnv.Cache executable.module.env tables memories := by
  rw [(w.initializers law).1]
  exact w.cache_input

end Itasca.Runtime.Compiler

end

/-! ## SegmentPayloadBounds -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ModuleBinary

private theorem vector_length_bound {α : Type} {R : α → List U8 → Prop} {values bytes}
    (encoded : VecEncoding R values bytes) : values.length < 2^32 := by
  obtain ⟨count, entries, bounded, _, _⟩ := encoded
  exact bounded.value_lt

private theorem element_payload_bound {entry bytes}
    (encoded : ElementEncodingFor entry bytes) : entry.init.length < 2^32 := by
  cases encoded with
  | activeIndices _ _ encoded | passiveIndices _ encoded | explicitIndices _ _ _ encoded
  | declarativeIndices _ encoded | activeExpressions _ _ encoded | passiveExpressions _ encoded
  | explicitExpressions _ _ _ encoded | declarativeExpressions _ encoded =>
    simpa using vector_length_bound encoded

private theorem data_payload_bound {entry bytes}
    (encoded : DataEncodingFor entry bytes) : entry.init.length < 2^32 := by
  cases encoded with
  | active _ _ encoded | passive _ encoded => exact vector_length_bound encoded

private theorem rep_property {α : Type} {R : α → List U8 → Prop} {Q : α → Prop} {values bytes}
    (encoded : Rep R values bytes) (property : ∀ value bytes, R value bytes → Q value) :
    ∀ value ∈ values, Q value := by
  induction encoded with
  | nil => simp
  | cons head tail ih =>
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact property _ _ head
    · exact ih value member

private theorem padded_property {α : Type} {R : α → List U8 → Prop} {Q : α → Prop} {id values bytes}
    (encoded : PaddedEncoding id (VecEncoding R) [] values bytes)
    (property : ∀ value bytes, R value bytes → Q value) : ∀ value ∈ values, Q value := by
  obtain ⟨customs, sec, _, secProof, _⟩ := encoded
  cases secProof with
  | absent => simp
  | present content =>
    obtain ⟨size, payload, _, ⟨count, entries, _, encoded, _⟩, _⟩ := content
    exact rep_property encoded property

/-- Binary vector prefixes bound every element and data payload, independently
of semantic typing and of the compiler's chosen instruction representation. -/
theorem module_segment_payload_bounds {R raw bytes}
    (encoded : ModuleEncodingWith R raw bytes) :
    (∀ element ∈ raw.elements, element.init.length < 2^32) ∧
    (∀ segment ∈ raw.data, segment.init.length < 2^32) := by
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
    codes, datas, customs, _, _, _, _, _, _, _, _, hel, _, _, hd, _, _, _⟩ := encoded
  exact ⟨padded_property hel (fun _ _ h => element_payload_bound h),
    padded_property hd (fun _ _ h => data_payload_bound h)⟩

/-- Payload bounds for the actual metadata retained by an accepted validator. -/
theorem validated_segment_payload_bounds {bytes module}
    (validated : Itasca.ModuleSound.Validated bytes module) :
    (∀ element ∈ module.env.elements.val, element.init.length < 2^32) ∧
    (∀ segment ∈ module.tail.data.val, segment.init.length < 2^32) := by
  obtain ⟨raw, encoded, _, matched, _⟩ := validated
  obtain ⟨elements, datas⟩ := module_segment_payload_bounds encoded
  have he := congrArg Itasca.ModuleBinary.Module.elements matched.1
  have hd := congrArg Itasca.ModuleBinary.Module.data matched.1
  constructor
  · intro element member
    apply elements (Itasca.ModuleEnv.rawElement element)
    rw [he]
    exact List.mem_map.mpr ⟨element, member, rfl⟩
  · intro segment member
    apply datas (Itasca.ModuleData.raw segment)
    rw [hd]
    exact List.mem_map.mpr ⟨segment, member, rfl⟩

/-- The public compiler supplies the payload bounds without an added count premise. -/
theorem compile_segment_payload_bounds {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits) (module : runtime.compiler.ExecutableModule)
    (accepted : runtime.compiler.compile_with allocator bytes limits = .ok (.Ok module)) :
    (∀ element ∈ module.module.env.elements.val, element.init.length < 2^32) ∧
    (∀ segment ∈ module.module.tail.data.val, segment.init.length < 2^32) := by
  exact validated_segment_payload_bounds (compile_source_validated allocator law bytes limits module accepted).1
end Itasca.Runtime.Compiler

end

/-! ## SourceInstantiation -/

section

namespace Itasca.Runtime.Compiler
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

theorem module_segment_counts {R raw bytes}
    (encoded : ModuleBinary.ModuleEncodingWith R raw bytes) :
    raw.elements.length < 2^32 ∧ raw.data.length < 2^32 := by
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
    codes, datas, customs, _, _, _, _, _, _, _, _, hel, _, _, hd, _, _, _⟩ := encoded
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
theorem source_instantiate {raw : ModuleBinary.Module} {R bytes}
    (encoded : ModuleBinary.ModuleEncodingWith R raw bytes)
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
end Itasca.Runtime.Compiler

end

/-! ## CompileDataCount -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual accepted tail validation agrees with every declared data count. -/
theorem CompileWitness.data_count_input {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness allocator bytes limits executable) :
    ∀ count, w.env.data_count = some count → count.val = w.tail.data.val.length := by
  obtain ⟨run⟩ := stream.validate_streaming.accepted
    runtime.compiler.CompileSource.Insts.ItascaStreamSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator)
    0#u64 {bytes, code_start := w.codeStart, code_end := w.codeEnd}
    (initialScheduler A limits w.codeStart) w.scheduler w.initialEnv w.env w.validated
  have tailDecoded := metadata.validate_tail_with.accepted_erase
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator).metadataModuleVisitorInst
    run.remaining.tailBytes 0#usize w.env run.remaining.region run.remaining.tail run.remaining.decodedTail
    run.remaining.decode_tail
  have tailSemantic := metadata.validate_tail.spec run.remaining.tailBytes 0#usize w.env (by simp)
  rw [tailDecoded, WP.spec_ok] at tailSemantic
  obtain ⟨_, _, count⟩ := tailSemantic
  have readyEq : run.remaining.ready = {run.remaining.decodedTail with tail := some run.remaining.tail} := by
    simpa only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.project_tail_ready.eq,
      runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.tail_ready.eq,
      Result.ok.injEq, Prod.mk.injEq, true_and] using run.remaining.ready_call.symm
  have drained := compiler_drain_frame allocator 0#u64 run.remaining.ready w.scheduler
    run.remaining.pending run.remaining.remaining run.remaining.drain_call
  have finalTail := congrArg runtime.compiler.CompileScheduler.tail drained
  simp only [readyEq, w.tailReady] at finalTail
  have sameTail : w.tail = run.remaining.tail := Option.some.inj finalTail
  simpa only [sameTail] using count

/-- Initializer lowering retains the canonical data-count agreement. -/
theorem CompileWitness.data_count {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness allocator bytes limits executable)
    (law : Platform.AllocCorrect allocator) :
    ∀ count, executable.module.env.data_count = some count →
      count.val = executable.module.tail.data.val.length := by
  rw [(w.initializers law).1]
  exact w.data_count_input

end Itasca.Runtime.Compiler

end
