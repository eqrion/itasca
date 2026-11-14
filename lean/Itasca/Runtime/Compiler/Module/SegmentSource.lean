import Itasca.Runtime.Compiler.Local.Callbacks.CallbackEquations
import Itasca.Runtime.Compiler.Module.CodeRegionComplete
import Itasca.Runtime.Compiler.Local.Relations.Segments.SegmentTranslation
import Itasca.Runtime.Compiler.Local.Capacity.GlobalAvailability

/-!
Sections, each formerly its own module: CompileSemantic, SegmentSource.
-/

/-! ## CompileSemantic -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Successful canonical environment and tail validation expose their checked
semantic facts before compiler assembly. No binary typing inversion or compiler
correctness premise is needed to recover these actual validator postconditions. -/
theorem CompileWitness.semantic_input {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness allocator bytes limits executable) :
    ModuleEnv.Valid w.env ∧
      (∀ segment ∈ w.tail.data.val, ModuleData.Valid w.env segment) := by
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
  obtain ⟨decls, represented, valid, _, _, before, sourcePrefix, span⟩ := semantic
  have tailDecoded := metadata.validate_tail_with.accepted_erase
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator).metadataModuleVisitorInst
    run.remaining.tailBytes 0#usize w.env run.remaining.region run.remaining.tail run.remaining.decodedTail
    run.remaining.decode_tail
  have tailSemantic := metadata.validate_tail.spec run.remaining.tailBytes 0#usize w.env (by simp)
  rw [tailDecoded, WP.spec_ok] at tailSemantic
  obtain ⟨_, segments, _⟩ := tailSemantic
  have readyEq : run.remaining.ready = {run.remaining.decodedTail with tail := some run.remaining.tail} := by
    simpa only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.project_tail_ready.eq,
      runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.tail_ready.eq,
      Result.ok.injEq, Prod.mk.injEq, true_and] using run.remaining.ready_call.symm
  have drained := compiler_drain_frame allocator 0#u64 run.remaining.ready w.scheduler
    run.remaining.pending run.remaining.remaining run.remaining.drain_call
  have finalTail := congrArg runtime.compiler.CompileScheduler.tail drained
  simp only [readyEq, w.tailReady] at finalTail
  have sameTail : w.tail = run.remaining.tail := Option.some.inj finalTail
  exact ⟨valid, by simpa only [sameTail] using segments⟩

/-- Canonical validity belongs to the exact metadata retained in the accepted
executable, including the data tail actually delivered to the compiler. -/
theorem CompileWitness.semantic {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness allocator bytes limits executable)
    (law : Platform.AllocCorrect allocator) :
    ModuleEnv.Valid executable.module.env ∧
      (∀ segment ∈ executable.module.tail.data.val, ModuleData.Valid executable.module.env segment) := by
  rw [(w.initializers law).1]
  exact w.semantic_input

/-- Actual successful public compilation constructs the retained segment program
certificate, using the canonical validator's checked active-offset typing. -/
theorem CompileWitness.segment_program {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness allocator bytes limits executable)
    (law : Platform.AllocCorrect allocator) :
    ∃ function, executable.functions.val[executable.initialization.val]? = some function ∧
      SegmentProgram executable function := by
  obtain ⟨valid, datas⟩ := w.semantic_input
  have elements : ∀ segment ∈ w.env.elements.val, ∀ table offset,
      segment.mode = .Active table offset → ModuleConstants.Valid w.env offset .I32 := by
    intro segment member table offset mode
    have typed := (valid.elements segment member).1
    obtain ⟨bound, tableType, offsetValid⟩ := (show ∃ h : table.val < w.env.table_types.val.length,
      w.env.table_types.val[table.val].elem = segment.elem ∧ ModuleConstants.Valid w.env offset .I32 from by simpa [mode] using typed)
    exact offsetValid
  have dataOffsets : ∀ segment ∈ w.tail.data.val, ∀ memory offset,
      segment.mode = .Active memory offset → ModuleConstants.Valid w.env offset .I32 := by
    intro segment member memory offset mode
    have typed := datas segment member
    exact (show memory.val < w.env.mem_types.val.length ∧ ModuleConstants.Valid w.env offset .I32 from
      by simpa [ModuleData.Valid, mode] using typed).2
  have result := initializer_lower_segments allocator law _ _ _ _ rfl rfl rfl rfl elements dataOffsets w.lowered
  exact result.2.2.2

end Itasca.Runtime.Compiler

end

/-! ## SegmentSource -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Accepted source bytes supply the binary framing and metadata coherence
needed by the retained initializer's program-counter bound. -/
theorem segment_validated_pc_bound {module function bytes}
    (certificate : SegmentProgram module function)
    (validated : Itasca.ModuleSound.Validated bytes module.module)
    (bounded : bytes.length ≤ Itasca.limits.MAX_MODULE_BYTES.val) :
    function.code.length < U32.max := by
  obtain ⟨raw, encoded, _, matched, _⟩ := validated
  have elements := congrArg (fun raw : Itasca.ModuleBinary.Module => raw.elements.length) matched.1
  have datas := congrArg (fun raw : Itasca.ModuleBinary.Module => raw.data.length) matched.1
  apply certificate.pc_bound encoded bounded
  · simpa [Itasca.ModuleElaboration.fromEnv] using elements.symm
  · simpa [Itasca.ModuleElaboration.fromEnv] using datas.symm

/-- No extra runtime limit premise is required for the initializer PC: the
successful public compiler already checked the fixed module-byte cap. -/
theorem segment_compile_pc_bound {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits) (module : runtime.compiler.ExecutableModule)
    (accepted : runtime.compiler.compile_with allocator bytes limits = .ok (.Ok module))
    (function : runtime.bytecode.CompiledFunction) (certificate : SegmentProgram module function) :
    function.code.length < U32.max := by
  obtain ⟨validated, bounded⟩ := compile_source_validated allocator law bytes limits module accepted
  exact segment_validated_pc_bound certificate validated bounded

end Itasca.Runtime.Compiler

end
