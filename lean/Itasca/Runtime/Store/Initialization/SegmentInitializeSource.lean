import Itasca.Runtime.Store.Initialization.SegmentSyntheticSource
import Itasca.Runtime.Store.Initialization.SegmentInitializePreservation
import Itasca.Runtime.Compiler.Local.Relations.Segments.SegmentFlowSource

/-!
Source correspondence and resource causes for complete segment initialization. Setup failures remain distinct from executed segment effects.
-/

/-! ## Segment Initialize Source -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

/-- Ordered source instructions for the retained element and data initialization programs. -/
def segmentModuleSource (module : runtime.compiler.ExecutableModule) : List admininstr :=
  (Spec.Segment.elementPrograms (module.module.env.elements.val.map (fun entry =>
    Itasca.ModuleElaboration.element (Itasca.ModuleEnv.rawElement entry)))).flatten.map admininstr_instr ++
  (Spec.Segment.dataPrograms (module.module.tail.data.val.map (fun entry =>
    Itasca.ModuleData.translate (Itasca.ModuleData.raw entry)))).flatten.map admininstr_instr

/-- Source program indexed by the independent binary module witness. -/
def segmentRawSource (raw : Itasca.ModuleBinary.Module) : List admininstr :=
  (Spec.Segment.elementPrograms (raw.elements.map Itasca.ModuleElaboration.element)).flatten.map admininstr_instr ++
  (Spec.Segment.dataPrograms (raw.data.map Itasca.ModuleData.translate)).flatten.map admininstr_instr

theorem segmentModuleSource_raw (module : runtime.compiler.ExecutableModule)
    (raw : Itasca.ModuleBinary.Module)
    (matched : Itasca.ModuleElaboration.Matches module.module.env module.module.tail raw) :
    segmentModuleSource module = segmentRawSource raw := by
  have elements := congrArg Itasca.ModuleBinary.Module.elements matched.1
  have datas := congrArg Itasca.ModuleBinary.Module.data matched.1
  simp only [segmentRawSource, elements, datas, Itasca.ModuleElaboration.fromEnv,
    List.map_map, Function.comp_def,segmentModuleSource]

end Itasca.Runtime.Store

end

/-! ## Segment Initialize Causes -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

/-- Exact setup cause for the actual compiled segment initializer. The function
lookup and checked syntactic program prevent an arbitrary slot demand witness. -/
def SegmentSetupCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (error : runtime.ExecError) : Prop :=
  ∃ code, module.functions.val[module.initialization.val]? = some code ∧
    Code.SegmentProgram module code ∧ Interp.SyntheticPreparationCause allocator store code error

theorem initialize_segments_source_causes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[inst.module.initialization.val]? = some code)
    (ready : SegmentCodeReady store inst code code.slot_count.val)
    (sourceCode : CodeInterpretation) (flow : Code.SegmentFlow 0 code.code.val)
    (compatible : ∀ instruction ∈ code.code.val, SegmentBulkCompatible store inst code instruction)
    (globals : ∀ index address value, .GlobalGet 0#u32 index ∈ code.code.val →
      inst.globals.val[index.val]? = some address → store.globals.val[address.index.val]? = some value → value.ty.valtype = .I32)
    (shape : Shape view store) (sourceSyntax : StoreSyntax sourceCode store) (bounds : SegmentBounds store)
    (ambient : frame) (ambientWf : wf_frame ambient) (moduleEq : ambient.MODULE = decodeInstance store inst) :
    runtime.interp.initialize_segments memory hooks floats allocator store platform instIndex
      ⦃ out => (∃ reason, out.1 = .Err (.Exhausted reason) ∧ out.2.1 = store ∧
        Interp.SyntheticPreparationCause allocator store code (.Exhausted reason)) ∨
        SegmentExecutionStatus out.1 ∧ StepsH ⟨⟨decodeStore view sourceCode store,ambient⟩,Code.segmentSource code code.code.val⟩ []
          ⟨⟨decodeStore view sourceCode out.2.1,ambient⟩, segmentResult out.1⟩ ⦄ := by
  unfold runtime.interp.initialize_segments
  step with Interp.vec_index_given store.instances instIndex inst found as ⟨actual, equal⟩
  subst actual
  step with segment_synthetic_source_causes memory hooks floats allocator view laws law store platform instIndex
    inst.module.initialization inst code found functionFound ready sourceCode flow compatible globals
    shape sourceSyntax bounds ambient ambientWf moduleEq as ⟨result,after,host,outcome⟩
  cases result <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,segmentResult,SegmentExecutionStatus]

/-- Accepted compilation supplies the complete segment program correspondence;
only setup exhaustion can precede the source execution. -/
theorem initialize_segments_compiled_source_causes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex : Usize)
    (inst : runtime.store.ModuleInst) (bytes : Slice U8) (profile : Itasca.ValidationProfile)
    (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module))
    (found : store.instances.val[instIndex.val]? = some inst)
    (sourceCode : CodeInterpretation) (shape : Shape view store)
    (sourceSyntax : StoreSyntax sourceCode store) (bounds : SegmentBounds store)
    (imports : InitializerImports store inst) (bindings : InitializerBindings store inst)
    (types : SegmentTypeBindings store inst)
    (ambient : frame) (ambientWf : wf_frame ambient) (moduleEq : ambient.MODULE = decodeInstance store inst) :
    runtime.interp.initialize_segments memory hooks floats allocator store platform instIndex
      ⦃ out => (∃ reason, out.1 = .Err (.Exhausted reason) ∧ out.2.1 = store ∧
        SegmentSetupCause allocator store inst.module (.Exhausted reason)) ∨
        SegmentExecutionStatus out.1 ∧ StepsH ⟨⟨decodeStore view sourceCode store,ambient⟩,segmentModuleSource inst.module⟩ []
          ⟨⟨decodeStore view sourceCode out.2.1,ambient⟩,segmentResult out.1⟩ ⦄ := by
  obtain ⟨witness⟩ := Code.compile_accepted allocator bytes profile limits inst.module accepted
  obtain ⟨code, functionFound, program⟩ := witness.segment_program law
  obtain ⟨valid, dataValid⟩ := witness.semantic law
  have pcBound := Code.segment_compile_pc_bound allocator law bytes profile limits inst.module accepted code program
  have instanceShape := shape.instances inst (List.mem_of_getElem? found)
  have ready := segment_program_ready store inst code program pcBound instanceShape imports bindings valid.elements dataValid
  have compatible := segment_program_compatible store inst code program types valid.elements
  have globals : ∀ index address value, .GlobalGet 0#u32 index ∈ code.code.val →
      inst.globals.val[index.val]? = some address → store.globals.val[address.index.val]? = some value → value.ty.valtype = .I32 := by
    intro index address value member mapped issued
    obtain ⟨ty,declared,integer,imported⟩ := program.global_types valid.elements dataValid 0#u32 index member
    obtain ⟨actualAddress,actualValue,actualMapped,actualIssued,actualType⟩ := imports.globals index ty declared imported
    have sameAddress := Option.some.inj (actualMapped.symm.trans mapped)
    subst actualAddress
    have sameValue := Option.some.inj (actualIssued.symm.trans issued)
    subst actualValue
    rw [actualType]
    exact integer
  have checked := initialize_segments_source_causes memory hooks floats allocator view laws law store platform instIndex inst code
    found functionFound ready sourceCode (program.flow valid.elements dataValid) compatible globals
    shape sourceSyntax bounds ambient ambientWf moduleEq
  apply WP.spec_mono checked
  intro out outcome
  rcases outcome with ⟨reason,failed,same,cause⟩ | reduced
  · exact Or.inl ⟨reason,failed,same,code,functionFound,program,cause⟩
  · exact Or.inr (by simpa only [program.source valid.elements dataValid,segmentModuleSource] using reduced)

/-- Segment initialization composes with the source start-call continuation.
Setup exhaustion leaves the store unchanged; successful writes reach the exact
continuation, while any range trap absorbs it. -/
theorem initialize_segments_raw_source_causes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex : Usize)
    (inst : runtime.store.ModuleInst) (bytes : Slice U8) (profile : Itasca.ValidationProfile)
    (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module))
    (found : store.instances.val[instIndex.val]? = some inst)
    (sourceCode : CodeInterpretation) (shape : Shape view store)
    (sourceSyntax : StoreSyntax sourceCode store) (bounds : SegmentBounds store)
    (imports : InitializerImports store inst) (bindings : InitializerBindings store inst)
    (types : SegmentTypeBindings store inst)
    (ambient : frame) (ambientWf : wf_frame ambient) (moduleEq : ambient.MODULE = decodeInstance store inst)
    (raw : Itasca.ModuleBinary.Module)
    (matched : Itasca.ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw)
    (after : List admininstr) (afterWf : Forall wf_admininstr after) :
    runtime.interp.initialize_segments memory hooks floats allocator store platform instIndex
      ⦃ out => (∃ reason, out.1 = .Err (.Exhausted reason) ∧ out.2.1 = store ∧
        SegmentSetupCause allocator store inst.module (.Exhausted reason)) ∨
        SegmentExecutionStatus out.1 ∧ StepsH ⟨⟨decodeStore view sourceCode store,ambient⟩,segmentRawSource raw ++ after⟩ []
          ⟨⟨decodeStore view sourceCode out.2.1,ambient⟩,segmentAfter out.1 after⟩ ⦄ := by
  obtain ⟨out,run,outcome⟩ := WP.spec_imp_exists (initialize_segments_compiled_source_causes
    memory hooks floats allocator view laws law store platform instIndex inst bytes profile limits
    accepted found sourceCode shape sourceSyntax bounds imports bindings types ambient ambientWf moduleEq)
  rw [run,WP.spec_ok]
  rcases outcome with exhausted | reduced
  · exact Or.inl exhausted
  · rcases reduced with ⟨status,reduced⟩
    refine Or.inr ⟨status,?_⟩
    have contextual := segment_steps_suffix _ _ _ out.1 after reduced afterWf
    simpa only [Spec.instrContext,vals,List.map_nil,List.nil_append,
      segmentModuleSource_raw inst.module raw matched] using contextual

end Itasca.Runtime.Store

end
