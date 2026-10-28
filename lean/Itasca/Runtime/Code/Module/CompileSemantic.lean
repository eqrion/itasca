import Itasca.Runtime.Code.Module.CompileSource
import Itasca.Runtime.Code.Local.Relations.Common.SegmentComplete

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Successful canonical environment and tail validation expose their checked
semantic facts before compiler assembly. No binary typing inversion or compiler
correctness premise is needed to recover these actual validator postconditions. -/
theorem CompileWitness.semantic_input {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes profile limits executable} (w : CompileWitness allocator bytes profile limits executable) :
    ModuleEnv.Valid w.env profile ∧
      (∀ segment ∈ w.tail.data.val, ModuleData.Valid w.env segment) := by
  obtain ⟨run⟩ := stream.validate_streaming.accepted
    runtime.compiler.CompileSource.Insts.ItascaStreamSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator)
    0#u64 {bytes, code_start := w.codeStart, code_end := w.codeEnd}
    (initialScheduler A limits w.codeStart) w.scheduler w.initialEnv w.env w.validated
  have decoded := module.validate_env_with.accepted_erase
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator).moduleModuleVisitorInst
    run.environment run.region w.env run.environmentLength run.decoded run.decode_environment
  have semantic := module.validate_env.profile_semantic_spec run.environment profile
  rw [decoded, WP.spec_ok] at semantic
  obtain ⟨decls, represented, valid, _, _, before, sourcePrefix, span⟩ := semantic
  have tailDecoded := module.validate_tail_with.accepted_erase
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator).moduleModuleVisitorInst
    run.remaining.tailBytes 0#usize w.env run.remaining.region run.remaining.tail run.remaining.decodedTail
    run.remaining.decode_tail
  have tailSemantic := module.validate_tail.spec run.remaining.tailBytes 0#usize w.env (by simp) profile
  rw [tailDecoded, WP.spec_ok] at tailSemantic
  obtain ⟨_, segments, _⟩ := tailSemantic
  have readyEq : run.remaining.ready = {run.remaining.decodedTail with tail := some run.remaining.tail} := by
    simpa only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor,
      runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.tail_ready,
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
    {bytes profile limits executable} (w : CompileWitness allocator bytes profile limits executable)
    (law : Platform.AllocCorrect allocator) :
    ModuleEnv.Valid executable.module.env profile ∧
      (∀ segment ∈ executable.module.tail.data.val, ModuleData.Valid executable.module.env segment) := by
  rw [(w.initializers law).1]
  exact w.semantic_input

/-- Actual successful public compilation constructs the retained segment program
certificate, using the canonical validator's checked active-offset typing. -/
theorem CompileWitness.segment_program {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes profile limits executable} (w : CompileWitness allocator bytes profile limits executable)
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
  exact result.2.2.2.2

end Itasca.Runtime.Code
