import Itasca.Runtime.Compiler.Local.Initializer.LowerContracts
import Itasca.Runtime.Compiler.Local.Initializer.SegmentLoopContracts
import Itasca.Runtime.Compiler.Local.Initializer.SegmentEmissionContracts
import Itasca.Runtime.Compiler.Local.Initializer.ElementContracts
import Itasca.Runtime.Compiler.Local.Initializer.ModuleLoopContracts
import Itasca.Runtime.Compiler.Local.Initializer.ElementLoopContracts
import Itasca.Runtime.Compiler.Local.Initializer.ElementValueContracts
import Itasca.Runtime.Compiler.Local.Initializer.DataOffsetContracts
import Itasca.Runtime.Compiler.Local.Initializer.GlobalContracts
import Itasca.Runtime.Compiler.Local.Initializer.ExpressionContracts
import Itasca.Runtime.Compiler.Local.Callbacks.CallbackEquations
import Itasca.Runtime.Compiler.Local.Initializer.ConstantContracts
import Itasca.Runtime.Compiler.Module.CodeRegionComplete
import Itasca.Runtime.Compiler.Local.Source.SourceSegmentPrograms
import Itasca.Runtime.Compiler.Module.CompileSubmit
import Itasca.Stream.SplitTotal
import Itasca.Runtime.Compiler.Local.Initializer.InitializerElementAppend
import Itasca.Runtime.Compiler.Local.Initializer

/-!
Sections, each formerly its own module: CompileSourceCertificate, CompileStreamSource, CompilerLargeEnvironment, InitializerTotalBasic, InitializerTotalMappings, InitializerTotal.
-/

/-! ## CompileSourceCertificate -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The canonical source syntax and exact code-region framing from an actual
public compilation. Keeping the accepted driver run fixes the configuration,
submission and tail states used by module certificate assembly. -/
structure CompileSourceCertificate {A : Type} {ops : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness ops bytes limits executable) where
  environment : Slice U8
  code : Slice U8
  tail : Slice U8
  run : StreamRun.Accepted runtime.compiler.CompileSource.Insts.ItascaStreamSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
    0#u64 {bytes, code_start := w.codeStart, code_end := w.codeEnd}
    (initialScheduler A limits w.codeStart) w.scheduler w.env
  coherent : StreamSource.Coherent runtime.compiler.CompileSource.Insts.ItascaStreamSource
    {bytes, code_start := w.codeStart, code_end := w.codeEnd} environment.val code.val tail.val
  recombined : bytes.val = environment.val ++ code.val ++ tail.val
  raw : ModuleBinary.Module
  encoded : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding) raw bytes.val
  matched : ModuleElaboration.Matches w.env run.remaining.tail raw
  valid : ModuleEnv.Valid w.env
  entryBounds : CodeEntry.Bounds w.env
  functions : raw.functions = w.env.func_type_indices.val
  types : raw.types = w.env.types.val
  codeCount : raw.codes.length = w.env.func_type_indices.val.length
  header : StreamFraming.HeaderAt code w.env run.remaining.entries
  entries : ModuleBinary.At (ModuleBinary.Rep (Profile.CodeEncoding)) code run.remaining.entries raw.codes (Slice.len code)
  codeBound : code.length ≤ Itasca.limits.MAX_MODULE_BYTES.val
  moduleBound : bytes.length ≤ Itasca.limits.MAX_MODULE_BYTES.val

theorem CompileWitness.source_certificate {A : Type} {ops : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness ops bytes limits executable)
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
  obtain ⟨raw, encoded, matched, valid, entryBounds, functions, types, codeCount,
    header, entries, codeBound, moduleBound⟩ := stream_run_source
    runtime.compiler.CompileSource.Insts.ItascaStreamSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
    SchedulerTracks (compiler_provenance ops law) 0#u64 source
    (initialScheduler A limits w.codeStart) w.scheduler w.env bytes environment code tail coherent recombine initial run
  exact ⟨⟨environment, code, tail, run, coherent, recombine, raw, encoded, matched, valid,
    entryBounds, functions, types, codeCount, header, entries, codeBound, moduleBound⟩⟩
end Itasca.Runtime.Compiler

end

/-! ## CompileStreamSource -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The actual successful streaming phase supplies source encoding and exact
module metadata before initializer lowering is attempted. -/
theorem compiler_stream_source {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits) (codeStart codeEnd : Usize)
    (storage env : metadata.Env) (scheduler : runtime.compiler.CompileScheduler A)
    (tail : metadata.Tail)
    (bounds : codeStart.val ≤ codeEnd.val ∧ codeEnd.val ≤ bytes.length)
    (tailReady : scheduler.tail = some tail)
    (accepted : stream.validate_streaming runtime.compiler.CompileSource.Insts.ItascaStreamSource
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops) 0#u64
      {bytes,code_start := codeStart,code_end := codeEnd}
      (initialScheduler A limits codeStart) storage = .ok (.Ok (),scheduler,env)) :
    ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding) raw bytes.val ∧
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
  obtain ⟨raw,encoded,matched,valid,entryBounds,functions,types,codeCount,
    header,entries,codeBound,moduleBound⟩ := stream_run_source
    runtime.compiler.CompileSource.Insts.ItascaStreamSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
    SchedulerTracks (compiler_provenance ops law) 0#u64 source
    (initialScheduler A limits codeStart) scheduler env bytes environment code tailBytes coherent recombine initial run
  have readyEq : run.remaining.ready = {run.remaining.decodedTail with tail := some run.remaining.tail} := by
    simpa only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.project_tail_ready.eq,
      runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.tail_ready.eq,
      Result.ok.injEq,Prod.mk.injEq,true_and] using run.remaining.ready_call.symm
  have drained := compiler_drain_frame ops 0#u64 run.remaining.ready scheduler
    run.remaining.pending run.remaining.remaining run.remaining.drain_call
  have finalTail := congrArg runtime.compiler.CompileScheduler.tail drained
  simp only [readyEq,tailReady] at finalTail
  have sameTail : tail = run.remaining.tail := Option.some.inj finalTail
  exact ⟨raw,encoded,by simpa only [sameTail] using matched,functions,moduleBound⟩
end Itasca.Runtime.Compiler

end

/-! ## CompilerLargeEnvironment -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- An oversized scanned environment is rejected before any compiler callback.
This covers custom compile limits larger than the validator's module cap. -/
theorem compiler_stream_large_environment {V : Type} (visitor : stream.StreamingVisitor V)
     (source : runtime.compiler.CompileSource)
    (bounds : SourceBounds source) (large : limits.MAX_MODULE_BYTES.val < source.code_start.val)
    (state : V) (storage : metadata.Env) :
    stream.validate_streaming runtime.compiler.CompileSource.Insts.ItascaStreamSource visitor
      0#u64 source state storage = .ok (.Err .ModuleTooLarge,state,storage) := by
  obtain ⟨_,environment,bytes,rfl,decoded⟩ := WP.spec_imp_exists (source_environment_spec source bounds)
  have length : bytes.length = source.code_start.val := by
    simp only [Slice.length,decoded,sourceEnvironment,List.length_take]
    have bound := bounds.1.trans bounds.2
    change source.code_start.val ≤ source.bytes.val.length at bound
    omega
  obtain ⟨result,checked,post⟩ := WP.spec_imp_exists (limits.add_offset.spec 0#usize (Slice.len bytes))
  have rejected : result = .Err .ModuleTooLarge := by
    cases result with
    | Err error => exact congrArg core.result.Result.Err post.1
    | Ok total =>
      have bound := post.2
      have count := post.1
      simp only [show (0#usize).val = 0 from rfl,Slice.len_val] at count
      omega
  simp only [Itasca.stream.validate_streaming]
  simp only [environment]
  simp only [bind_ok,core.result.Result.Insts.CoreOpsTry.branch]
  rw [checked,rejected]
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
end Itasca.Runtime.Compiler

end

/-! ## InitializerTotalBasic -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std



end Itasca.Runtime.Compiler

end

/-! ## InitializerTotalMappings -/

section

/-!
Normal return of element initializer values and the initializer mapping loops.
-/

/-! ## Initializer Total Element -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem initializer_element_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (i : Usize) (segment : Itasca.metadata.Element)
    (found : m.module.env.elements.val[i.val]? = some segment)
    (space : initializerSize m + segment.init.val.length + 3 ≤ Usize.max) :
    runtime.compiler.initialize.lower_element ops m budget i ⦃ out =>
      out.2.1.module = m.module ∧
      initializerSize out.2.1 ≤ initializerSize m + segment.init.val.length + 3 ⦄ := by
  exact runtime.compiler.initialize.lower_element.total ops law m budget i segment found space

end Itasca.Runtime.Compiler

end

/-! ## Initializer Total Mappings -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std






end Itasca.Runtime.Compiler

end

end

/-! ## InitializerTotal -/

section

/-!
Normal return of initializer emission and segment loops, composed into complete initializer lowering.
-/

/-! ## Initializer Total Emit -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- A single segment emits at most five instructions, one vector constant,
and one table-index pair. The bounds include rejected partial emissions. -/
@[step] theorem initializer_emit_element_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (bound : index.val < m.module.env.elements.val.length)
    (codeFits : function.code.val.length + 5 ≤ Usize.max)
    (poolFits : function.v128_pool.val.length + 1 ≤ Usize.max)
    (pairFits : function.indirect.val.length + 1 ≤ Usize.max) :
    runtime.compiler.initialize.emit_element ops m budget function index ⦃ out =>
      out.2.2.code.val.length ≤ function.code.val.length + 5 ∧
      out.2.2.v128_pool.val.length ≤ function.v128_pool.val.length + 1 ∧
      out.2.2.indirect.val.length ≤ function.indirect.val.length + 1 ⦄ := by
  exact runtime.compiler.initialize.emit_element.total ops law m budget function index bound codeFits poolFits pairFits

@[step] theorem initializer_emit_data_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (bound : index.val < m.module.tail.data.val.length)
    (codeFits : function.code.val.length + 5 ≤ Usize.max)
    (poolFits : function.v128_pool.val.length + 1 ≤ Usize.max) :
    runtime.compiler.initialize.emit_data ops m budget function index ⦃ out =>
      out.2.2.code.val.length ≤ function.code.val.length + 5 ∧
      out.2.2.v128_pool.val.length ≤ function.v128_pool.val.length + 1 ∧
      out.2.2.indirect = function.indirect ⦄ := by
  exact runtime.compiler.initialize.emit_data.total ops law m budget function index bound codeFits poolFits

end Itasca.Runtime.Compiler

end

/-! ## Initializer Total Segments -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std



end Itasca.Runtime.Compiler

end

/-! ## Initializer Total -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096


/-- Initializer lowering returns normally under its finite append headroom.
These quantitative input bounds concern internal vectors, not correctness of
compiled code or normal return of a subcomputation. Every allocator refusal,
instruction-budget rejection, and checker rejection is included. -/
@[step] theorem initializer_lower_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A)
    (mapSpace : initializerSize m + initializerMappingCost m.module + 1 ≤ Usize.max)
    (segmentSpace : 5 * (m.module.env.elements.val.length + m.module.tail.data.val.length) + 1 ≤ Usize.max) :
    runtime.compiler.initialize.lower ops m budget ⦃ out =>
      out.2.1.module = m.module ∧
      initializerSize out.2.1 ≤ initializerSize m + initializerMappingCost m.module + 1 ⦄ := by
  exact runtime.compiler.initialize.lower.total ops law m budget mapSpace segmentSpace

/-- Driver-facing form: initializer maps are freshly empty, so only source
counts and the already compiled function count consume the retained allowance. -/
theorem initializer_lower_fresh_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A)
    (globals : m.global_initializers.val = [])
    (elements : m.element_initializers.val = [])
    (elementOffsets : m.element_offsets.val = [])
    (dataOffsets : m.data_offsets.val = [])
    (mapSpace : m.functions.val.length + initializerMappingCost m.module + 1 ≤ Usize.max)
    (segmentSpace : 5 * (m.module.env.elements.val.length + m.module.tail.data.val.length) + 1 ≤ Usize.max) :
    runtime.compiler.initialize.lower ops m budget ⦃ _ => True ⦄ := by
  have headroom : initializerSize m + initializerMappingCost m.module + 1 ≤ Usize.max := by
    simpa [initializerSize, globals, elements, elementOffsets, dataOffsets] using mapSpace
  apply WP.spec_mono (initializer_lower_total ops law m budget headroom segmentSpace)
  intros; trivial

end Itasca.Runtime.Compiler

end

end
