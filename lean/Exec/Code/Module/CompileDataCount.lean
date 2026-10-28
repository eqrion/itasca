import Exec.Code.Module.CompileSemantic
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Actual accepted tail validation agrees with every declared data count. -/
theorem CompileWitness.data_count_input {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes profile limits executable} (w : CompileWitness allocator bytes profile limits executable) :
    ∀ count, w.env.data_count = some count → count.val = w.tail.data.val.length := by
  obtain ⟨run⟩ := stream.validate_streaming.accepted
    runtime.compiler.CompileSource.Insts.ItascaStreamSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator)
    0#u64 {bytes, code_start := w.codeStart, code_end := w.codeEnd}
    (initialScheduler A limits w.codeStart) w.scheduler w.initialEnv w.env w.validated
  have tailDecoded := module.validate_tail_with.accepted_erase
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator).moduleModuleVisitorInst
    run.remaining.tailBytes 0#usize w.env run.remaining.region run.remaining.tail run.remaining.decodedTail
    run.remaining.decode_tail
  have tailSemantic := module.validate_tail.spec run.remaining.tailBytes 0#usize w.env (by simp) profile
  rw [tailDecoded, WP.spec_ok] at tailSemantic
  obtain ⟨_, _, count⟩ := tailSemantic
  have readyEq : run.remaining.ready = {run.remaining.decodedTail with tail := some run.remaining.tail} := by
    simpa only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor,
      runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.tail_ready,
      Result.ok.injEq, Prod.mk.injEq, true_and] using run.remaining.ready_call.symm
  have drained := compiler_drain_frame allocator 0#u64 run.remaining.ready w.scheduler
    run.remaining.pending run.remaining.remaining run.remaining.drain_call
  have finalTail := congrArg runtime.compiler.CompileScheduler.tail drained
  simp only [readyEq, w.tailReady] at finalTail
  have sameTail : w.tail = run.remaining.tail := Option.some.inj finalTail
  simpa only [sameTail] using count

/-- Initializer lowering retains the canonical data-count agreement. -/
theorem CompileWitness.data_count {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes profile limits executable} (w : CompileWitness allocator bytes profile limits executable)
    (law : Platform.AllocCorrect allocator) :
    ∀ count, executable.module.env.data_count = some count →
      count.val = executable.module.tail.data.val.length := by
  rw [(w.initializers law).1]
  exact w.data_count_input

end Itasca.Runtime.Code
