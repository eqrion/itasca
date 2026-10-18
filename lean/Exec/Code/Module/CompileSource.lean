import Exec.Code.Module.CompileAssembly
import Exec.Code.Module.CompilerDrain
import Exec.Code.Module.CodeRegion
import Itasca.Stream.DriverSound
namespace Exec.Code
open Aeneas Aeneas.Std
open Itasca

/-- The concrete source scanner and compiler scheduler discharge all embedding
premises of the existing validator's accepted-module theorem. -/
theorem CompileWitness.source_validated {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes profile limits executable} (w : CompileWitness allocator bytes profile limits executable)
    (law : Platform.AllocCorrect allocator) :
    ModuleSound.Validated bytes executable.module profile ∧ bytes.length ≤ Itasca.limits.MAX_MODULE_BYTES.val := by
  have bounds := code_region_spec bytes
  rw [w.region, WP.spec_ok] at bounds
  let source : runtime.compiler.CompileSource := {bytes, code_start := w.codeStart, code_end := w.codeEnd}
  have bounded : SourceBounds source := bounds
  have available := source_available source bounded
  obtain ⟨environment, _, he⟩ := available.environment_read
  obtain ⟨tail, _, ht⟩ := available.tail_read
  obtain ⟨len, _, hl⟩ := available.code_len_read
  obtain ⟨code, _, hc⟩ := available.code_read 0#usize len (by scalar_tac) (by omega)
  have hc' : code.val = sourceCode source := by
    simpa [List.slice, hl] using hc
  have coherent : StreamSource.Coherent runtime.compiler.CompileSource.Insts.ItascaStreamSource source
      environment.val code.val tail.val := by
    rw [he, hc', ht]
    exact source_coherent source bounded
  have recombine : bytes.val = environment.val ++ code.val ++ tail.val := by
    rw [he, hc', ht]
    exact (source_recombine source bounded).symm
  have initial : SchedulerTracks 0#u64 [] (initialScheduler A limits w.codeStart) := by
    constructor
    · simp
    · simp [initialScheduler]
  obtain ⟨run, validated, size⟩ := stream.validate_streaming.profile_sound
    runtime.compiler.CompileSource.Insts.ItascaStreamSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator)
    SchedulerTracks (compiler_provenance allocator law profile) 0#u64 source
    (initialScheduler A limits w.codeStart) w.scheduler w.initialEnv w.env bytes environment code tail
    coherent recombine initial w.validated
  have readyEq : run.remaining.ready = {run.remaining.decodedTail with tail := some run.remaining.tail} := by
    simpa only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor,
      runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.tail_ready,
      Result.ok.injEq, Prod.mk.injEq, true_and] using run.remaining.ready_call.symm
  have drained := compiler_drain_frame allocator 0#u64 run.remaining.ready w.scheduler
    run.remaining.pending run.remaining.remaining run.remaining.drain_call
  have finalTail := congrArg runtime.compiler.CompileScheduler.tail drained
  simp only [readyEq, w.tailReady] at finalTail
  have sameTail : w.tail = run.remaining.tail := Option.some.inj finalTail
  refine ⟨?_, size⟩
  rw [(w.initializers law).1]
  simpa only [sameTail] using validated

/-- Every accepted public compilation validates exactly its input bytes under
the requested profile. This theorem makes no compiler-certificate premise. -/
theorem compile_source_validated {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (bytes : Slice U8) (profile : ValidationProfile)
    (limits : runtime.compiler.CompileLimits) (executable : runtime.compiler.ExecutableModule)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok executable)) :
    ModuleSound.Validated bytes executable.module profile ∧ executable.profile = profile ∧
      bytes.length ≤ Itasca.limits.MAX_MODULE_BYTES.val := by
  obtain ⟨w⟩ := compile_accepted allocator bytes profile limits executable accepted
  obtain ⟨validated, size⟩ := w.source_validated law
  exact ⟨validated, (w.initializers law).2.1, size⟩
end Exec.Code
