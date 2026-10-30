import Itasca.Runtime.Compiler.Module.CompileSourceCertificate
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The actual successful streaming phase supplies source encoding and exact
module metadata before initializer lowering is attempted. -/
theorem compiler_stream_source {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8) (profile : ValidationProfile)
    (limits : runtime.compiler.CompileLimits) (codeStart codeEnd : Usize)
    (storage env : metadata.Env) (scheduler : runtime.compiler.CompileScheduler A)
    (tail : metadata.Tail)
    (bounds : codeStart.val ≤ codeEnd.val ∧ codeEnd.val ≤ bytes.length)
    (tailReady : scheduler.tail = some tail)
    (accepted : stream.validate_streaming runtime.compiler.CompileSource.Insts.ItascaStreamSource
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops) 0#u64 profile
      {bytes,code_start := codeStart,code_end := codeEnd}
      (initialScheduler A limits codeStart) storage = .ok (.Ok (),scheduler,env)) :
    ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧
      ModuleElaboration.Matches env tail raw ∧ raw.functions = env.func_type_indices.val ∧
      bytes.length ≤ Itasca.limits.MAX_MODULE_BYTES.val := by
  let source : runtime.compiler.CompileSource := {bytes,code_start := codeStart,code_end := codeEnd}
  have bounded : SourceBounds source := bounds
  have available := source_available source bounded
  obtain ⟨environment,_,he⟩ := available.environment_read
  obtain ⟨tailBytes,_,ht⟩ := available.tail_read
  obtain ⟨len,_,hl⟩ := available.code_len_read
  obtain ⟨code,_,hc⟩ := available.code_read 0#usize len (by scalar_tac) (by omega)
  have hc' : code.val = sourceCode source := by simpa [List.slice,hl] using hc
  have coherent : StreamSource.Coherent runtime.compiler.CompileSource.Insts.ItascaStreamSource
      source environment.val code.val tailBytes.val := by
    rw [he,hc',ht]
    exact source_coherent source bounded
  have recombine : bytes.val = environment.val ++ code.val ++ tailBytes.val := by
    rw [he,hc',ht]
    exact (source_recombine source bounded).symm
  have initial : SchedulerTracks 0#u64 [] (initialScheduler A limits codeStart) := by
    constructor
    · simp
    · simp [initialScheduler]
  obtain ⟨run⟩ := stream.validate_streaming.accepted
    runtime.compiler.CompileSource.Insts.ItascaStreamSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
    0#u64 source (initialScheduler A limits codeStart) scheduler storage env accepted
  obtain ⟨raw,encoded,matched,valid,entryBounds,environmentProfile,functions,types,codeCount,
    header,entries,codeBound,moduleBound⟩ := stream_run_source
    runtime.compiler.CompileSource.Insts.ItascaStreamSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
    SchedulerTracks (compiler_provenance ops law profile) 0#u64 source
    (initialScheduler A limits codeStart) scheduler env bytes environment code tailBytes coherent recombine initial run
  have readyEq : run.remaining.ready = {run.remaining.decodedTail with tail := some run.remaining.tail} := by
    simpa only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor,
      runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.tail_ready,
      Result.ok.injEq,Prod.mk.injEq,true_and] using run.remaining.ready_call.symm
  have drained := compiler_drain_frame ops 0#u64 run.remaining.ready scheduler
    run.remaining.pending run.remaining.remaining run.remaining.drain_call
  have finalTail := congrArg runtime.compiler.CompileScheduler.tail drained
  simp only [readyEq,tailReady] at finalTail
  have sameTail : tail = run.remaining.tail := Option.some.inj finalTail
  exact ⟨raw,encoded,by simpa only [sameTail] using matched,functions,moduleBound⟩
end Itasca.Runtime.Compiler
