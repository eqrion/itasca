import Itasca.Runtime.Compiler.Module.CompileSource
import Itasca.Runtime.Compiler.Local.Source.SourceRun
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- The canonical source syntax and exact code-region framing from an actual
public compilation. Keeping the accepted driver run fixes the configuration,
submission and tail states used by module certificate assembly. -/
structure CompileSourceCertificate {A : Type} {ops : runtime.platform.Alloc A}
    {bytes profile limits executable} (w : CompileWitness ops bytes profile limits executable) where
  environment : Slice U8
  code : Slice U8
  tail : Slice U8
  run : StreamRun.Accepted runtime.compiler.CompileSource.Insts.ItascaStreamSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
    0#u64 {bytes, code_start := w.codeStart, code_end := w.codeEnd}
    (initialScheduler A limits w.codeStart) w.scheduler w.env profile
  coherent : StreamSource.Coherent runtime.compiler.CompileSource.Insts.ItascaStreamSource
    {bytes, code_start := w.codeStart, code_end := w.codeEnd} environment.val code.val tail.val
  recombined : bytes.val = environment.val ++ code.val ++ tail.val
  raw : ModuleBinary.Module
  encoded : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile
  matched : ModuleElaboration.Matches w.env run.remaining.tail raw
  valid : ModuleEnv.Valid w.env profile
  entryBounds : CodeEntry.Bounds w.env
  environmentProfile : Profile.Environment profile w.env
  functions : raw.functions = w.env.func_type_indices.val
  types : raw.types = w.env.types.val
  codeCount : raw.codes.length = w.env.func_type_indices.val.length
  header : StreamFraming.HeaderAt code w.env run.remaining.entries
  entries : ModuleBinary.At (ModuleBinary.Rep (Profile.CodeEncoding profile)) code run.remaining.entries raw.codes (Slice.len code)
  codeBound : code.length ≤ Itasca.limits.MAX_MODULE_BYTES.val
  moduleBound : bytes.length ≤ Itasca.limits.MAX_MODULE_BYTES.val

theorem CompileWitness.source_certificate {A : Type} {ops : runtime.platform.Alloc A}
    {bytes profile limits executable} (w : CompileWitness ops bytes profile limits executable)
    (law : Platform.AllocCorrect ops) : Nonempty (CompileSourceCertificate w) := by
  have bounds := code_region_spec bytes
  rw [w.region, WP.spec_ok] at bounds
  let source : runtime.compiler.CompileSource := {bytes, code_start := w.codeStart, code_end := w.codeEnd}
  have bounded : SourceBounds source := bounds
  have available := source_available source bounded
  obtain ⟨environment, _, he⟩ := available.environment_read
  obtain ⟨tail, _, ht⟩ := available.tail_read
  obtain ⟨len, _, hl⟩ := available.code_len_read
  obtain ⟨code, _, hc⟩ := available.code_read 0#usize len (by scalar_tac) (by omega)
  have hc' : code.val = sourceCode source := by simpa [List.slice, hl] using hc
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
  obtain ⟨run⟩ := stream.validate_streaming.accepted
    runtime.compiler.CompileSource.Insts.ItascaStreamSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
    0#u64 source (initialScheduler A limits w.codeStart) w.scheduler w.initialEnv w.env w.validated
  obtain ⟨raw, encoded, matched, valid, entryBounds, environmentProfile, functions, types, codeCount,
    header, entries, codeBound, moduleBound⟩ := stream_run_source
    runtime.compiler.CompileSource.Insts.ItascaStreamSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
    SchedulerTracks (compiler_provenance ops law profile) 0#u64 source
    (initialScheduler A limits w.codeStart) w.scheduler w.env bytes environment code tail coherent recombine initial run
  exact ⟨⟨environment, code, tail, run, coherent, recombine, raw, encoded, matched, valid,
    entryBounds, environmentProfile, functions, types, codeCount, header, entries, codeBound, moduleBound⟩⟩
end Itasca.Runtime.Code
