import Itasca.Runtime.Compiler.Module.CodeRegionComplete
import Itasca.Runtime.Compiler.Local.Source.SourceSegmentPrograms
import Itasca.Runtime.Compiler.Module.CompileSubmit
import Itasca.Stream.DriverTotal
import Itasca.Runtime.Compiler.Local.Initializer.InitializerElementAppend

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
set_option maxHeartbeats 1500000

/-- Combined retained-vector size, used only to account for append headroom. -/
def initializerSize (m : runtime.compiler.ExecutableModule) : Nat :=
  m.functions.val.length + m.global_initializers.val.length +
  m.element_initializers.val.length + m.element_offsets.val.length + m.data_offsets.val.length

@[step] theorem initializer_push_total {A T : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (values : alloc.vec.Vec T) (value : T) (fits : values.val.length < Usize.max) :
    runtime.compiler.Budget.push ops budget values value ⦃ out =>
      out.2.2.val.length ≤ values.val.length + 1 ⦄ := by
  apply WP.spec_mono (budget_push ops law budget values value fits)
  rintro ⟨status, nextBudget, next⟩ (⟨_, _, h⟩ | ⟨_, h, _⟩)
  · simp [h]
  · change next = values at h
    simp [h]

/-- Expression compilation is total with one available retained-function slot.
The bytecode checker is total even when it rejects the synthetic function. -/
@[step] theorem initializer_expression_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (expr : Itasca.wasm_types.ConstExpr)
    (ty : Itasca.wasm_types.ValueType) (space : initializerSize m + 1 ≤ Usize.max) :
    runtime.compiler.initialize.expression ops m budget expr ty ⦃ out =>
      out.2.1.module = m.module ∧ initializerSize out.2.1 ≤ initializerSize m + 1 ⦄ := by
  unfold runtime.compiler.initialize.expression
  rw [compiler_width_eq, bind_ok, initializer_synthetic, bind_ok]
  have codeFits : (initializerSeed ty).code.val.length < Usize.max := by
    simp [initializerSeed]; scalar_tac
  have poolFits : (initializerSeed ty).v128_pool.val.length < Usize.max := by
    simp [initializerSeed]; scalar_tac
  step with initializer_constant ops law budget (initializerSeed ty) expr ty 0#u32 codeFits poolFits
    as ⟨status, budget1, function, lowered⟩
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok unit =>
    cases unit
    obtain ⟨code, pool, instruction, functionEq, codeEq, _⟩ := lowered rfl
    have fits : function.code.val.length < Usize.max := by
      simp [functionEq, codeEq, initializerSeed]; scalar_tac
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with initializer_emit ops law budget1 function.code _ fits as ⟨status, budget2, finalCode, _⟩
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with well_formed_total { function with code := finalCode } as ⟨valid, _⟩
      cases valid with
      | false => simp
      | true =>
        simp only [↓reduceIte]
        have capacity : m.functions.val.length < Usize.max := by unfold initializerSize at space; omega
        step with initializer_push_total ops law budget2 m.functions _ capacity as ⟨status, budget3, functions, size⟩
        cases status <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          initializerSize] <;> omega

@[step] theorem initializer_global_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (index : Usize)
    (bound : index.val < m.module.env.globals.val.length)
    (space : initializerSize m + 2 ≤ Usize.max) :
    runtime.compiler.initialize.lower_global ops m budget index ⦃ out =>
      out.2.1.module = m.module ∧ initializerSize out.2.1 ≤ initializerSize m + 2 ⦄ := by
  unfold runtime.compiler.initialize.lower_global
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.globals, bind_ok]
  step as ⟨g, found⟩
  · simpa [alloc.vec.Vec.deref] using bound
  step with initializer_expression_total ops law m budget g.init g.gtype.valtype (by omega)
    as ⟨status, middle, budget1, same, size⟩
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, same]; omega
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have capacity : middle.global_initializers.val.length < Usize.max := by
      unfold initializerSize at size space; omega
    step with initializer_push_total ops law budget1 middle.global_initializers value capacity
      as ⟨status, budget2, values, count⟩
    try simp only [WP.spec_ok]
    exact ⟨same, by unfold initializerSize at *; dsimp; omega⟩

@[step] theorem initializer_data_offset_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (index : Usize)
    (bound : index.val < m.module.tail.data.val.length)
    (space : initializerSize m + 2 ≤ Usize.max) :
    runtime.compiler.initialize.lower_data_offset ops m budget index ⦃ out =>
      out.2.1.module = m.module ∧ initializerSize out.2.1 ≤ initializerSize m + 2 ⦄ := by
  unfold runtime.compiler.initialize.lower_data_offset
  simp only [runtime.compiler.ExecutableModule.tail,
    Itasca.metadata.Module.impl.tail, bind_ok]
  step as ⟨segment, found⟩
  cases mode : segment.mode with
  | Active memory offset =>
    simp only [mode]
    step with initializer_expression_total ops law m budget offset .I32 (by omega)
      as ⟨status, middle, budget1, same, size⟩
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, same]; omega
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have capacity : middle.data_offsets.val.length < Usize.max := by
        unfold initializerSize at size space; omega
      step with initializer_push_total ops law budget1 middle.data_offsets (some value) capacity
        as ⟨status, budget2, values, count⟩
      try simp only [WP.spec_ok]
      exact ⟨same, by unfold initializerSize at *; dsimp; omega⟩
  | Passive =>
    simp only [mode]
    have capacity : m.data_offsets.val.length < Usize.max := by unfold initializerSize at space; omega
    step with initializer_push_total ops law budget m.data_offsets none capacity
      as ⟨status, budget1, values, count⟩
    try simp only [WP.spec_ok]
    unfold initializerSize at *
    dsimp at *
    omega
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
set_option maxHeartbeats 1800000

@[step] theorem initializer_element_value_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (indices : alloc.vec.Vec Usize) (i j : Usize)
    (segment : Itasca.metadata.Element)
    (found : m.module.env.elements.val[i.val]? = some segment)
    (bound : j.val < segment.init.val.length) (capacity : indices.val.length < Usize.max)
    (space : initializerSize m + 1 ≤ Usize.max) :
    runtime.compiler.initialize.lower_element_value ops m budget indices i j ⦃ out =>
      out.2.1.module = m.module ∧ initializerSize out.2.1 ≤ initializerSize m + 1 ∧
      out.2.2.2.val.length ≤ indices.val.length + 1 ⦄ := by
  unfold runtime.compiler.initialize.lower_element_value
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok]
  rw [initializer_slice_index _ _ segment (by simpa [alloc.vec.Vec.deref] using found), bind_ok]
  step as ⟨expr, read⟩
  try simp only [bind_ok]
  have tyEq : wasm_types.ElemType.value_type segment.elem =
      .ok (Itasca.ModuleConstants.referenceValueType segment.elem) := by cases segment.elem <;> rfl
  rw [tyEq, bind_ok]
  step with initializer_expression_total ops law m budget expr _ space
    as ⟨status, middle, nextBudget, same, size⟩
  cases status with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, same, size]
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with initializer_push_total ops law nextBudget indices value capacity
      as ⟨status, finalBudget, nextIndices, count⟩
    exact ⟨same, size, count⟩

@[step] theorem initializer_element_values_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (i : Usize) (indices : alloc.vec.Vec Usize) (j : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError) (segment : Itasca.metadata.Element)
    (found : m.module.env.elements.val[i.val]? = some segment)
    (bound : j.val ≤ segment.init.val.length) (indicesBound : indices.val.length ≤ j.val)
    (space : initializerSize m + (segment.init.val.length - j.val) ≤ Usize.max) :
    runtime.compiler.initialize.lower_element_loop ops m budget i indices j status ⦃ out =>
      out.1.module = m.module ∧
      initializerSize out.1 ≤ initializerSize m + (segment.init.val.length - j.val) ⦄ := by
  unfold runtime.compiler.initialize.lower_element_loop
  apply loop.spec_decr_nat (fun st => segment.init.val.length - st.2.2.2.1.val)
    (fun st => st.1.module = m.module ∧
      initializerSize st.1 + (segment.init.val.length - st.2.2.2.1.val) ≤
        initializerSize m + (segment.init.val.length - j.val) ∧
      st.2.2.1.val.length ≤ st.2.2.2.1.val ∧ st.2.2.2.1.val ≤ segment.init.val.length)
  · rintro ⟨current, b, ix, position, result⟩ ⟨same, size, ixBound, positionBound⟩
    unfold runtime.compiler.initialize.lower_element_loop.body
    dsimp only at *
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok]
    rw [initializer_slice_index _ _ segment (by simpa [alloc.vec.Vec.deref, same] using found), bind_ok]
    split
    · rename_i more
      have posLt : position.val < segment.init.val.length := by scalar_tac
      cases result with
      | Err error => simp [core.result.Result.is_ok, same]; omega
      | Ok value =>
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with initializer_element_value_total ops law current b ix i position segment
          (by simpa [same] using found) posLt
          (by have := segment.init.property; omega) (by omega)
          as ⟨status, next, b1, ix1, source, growth, indexGrowth⟩
        step as ⟨nextPosition, increment⟩
        refine ⟨source.trans same, ?_, ?_, ?_, ?_⟩ <;> scalar_tac
    · simp only [WP.spec_ok]
      exact ⟨same, by omega⟩
  · exact ⟨rfl, Nat.le_refl _, indicesBound, bound⟩

@[step] theorem initializer_element_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (i : Usize) (segment : Itasca.metadata.Element)
    (found : m.module.env.elements.val[i.val]? = some segment)
    (space : initializerSize m + segment.init.val.length + 3 ≤ Usize.max) :
    runtime.compiler.initialize.lower_element ops m budget i ⦃ out =>
      out.2.1.module = m.module ∧
      initializerSize out.2.1 ≤ initializerSize m + segment.init.val.length + 3 ⦄ := by
  unfold runtime.compiler.initialize.lower_element
  step with initializer_element_values_total ops law m budget i (alloc.vec.Vec.new _) 0#usize
    (.Ok ()) segment found (by simp) (by simp) (by simpa using (show initializerSize m + segment.init.val.length ≤ Usize.max by omega))
    as ⟨middle, b1, indices, status, same, size⟩
  change initializerSize middle ≤ initializerSize m + segment.init.val.length at size
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, same]; omega
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with initializer_push_total ops law b1 middle.element_initializers indices
      (by unfold initializerSize at size space; omega) as ⟨status, b2, rows, rowsBound⟩
    cases status with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame, bind_ok, bind_tc_ok, WP.spec_ok]
      exact ⟨same, by unfold initializerSize at *; dsimp at *; omega⟩
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        runtime.compiler.ExecutableModule.env,
        Itasca.metadata.Module.impl.env, runtime.compiler.initialize.element_offset, Itasca.metadata.Env.impl.elements]
      try simp only [bind_ok]
      rw [initializer_slice_index _ _ segment (by simpa [alloc.vec.Vec.deref, same] using found), bind_ok]
      have room : initializerSize { middle with element_initializers := rows } + 2 ≤ Usize.max := by
        unfold initializerSize at *; dsimp at *; omega
      have middleSize : initializerSize { middle with element_initializers := rows } ≤
          initializerSize m + segment.init.val.length + 1 := by
        unfold initializerSize at *; dsimp at *; omega
      cases mode : segment.mode with
      | Active table offset =>
        simp only [mode, bind_ok]
        step with initializer_expression_total ops law { middle with element_initializers := rows }
          b2 offset .I32 (by omega) as ⟨status, final, b3, source, growth⟩
        cases status with
        | Err error =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame, bind_ok, bind_tc_ok, WP.spec_ok]
          exact ⟨source.trans same, by omega⟩
        | Ok index =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          step with initializer_push_total ops law b3 final.element_offsets (some index)
            (by unfold initializerSize at room growth; omega) as ⟨status, b4, offsets, offsetsBound⟩
          exact ⟨source.trans same, by unfold initializerSize at *; dsimp at *; omega⟩
      | Passive | Declarative =>
        simp only [mode, bind_ok]
        step with initializer_push_total ops law b2 middle.element_offsets none
          (by unfold initializerSize at room; dsimp at room; omega) as ⟨status, b3, offsets, offsetsBound⟩
        exact ⟨same, by unfold initializerSize at *; dsimp at *; omega⟩
end Itasca.Runtime.Compiler

end

/-! ## Initializer Total Mappings -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxHeartbeats 1800000

@[step] theorem initializer_mapping_loop0_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (i : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (space : initializerSize m + 2 * (m.module.env.globals.val.length - i.val) ≤ Usize.max) :
    runtime.compiler.initialize.lower_loop0 ops m budget i status ⦃ out =>
      out.1.module = m.module ∧
      initializerSize out.1 ≤ initializerSize m + 2 * (m.module.env.globals.val.length - i.val) ⦄ := by
  unfold runtime.compiler.initialize.lower_loop0
  apply loop.spec_decr_nat (fun st => m.module.env.globals.val.length - st.2.2.1.val)
    (fun st => st.1.module = m.module ∧
      initializerSize st.1 + 2 * (m.module.env.globals.val.length - st.2.2.1.val) ≤
        initializerSize m + 2 * (m.module.env.globals.val.length - i.val))
  · rintro ⟨current, b, index, result⟩ ⟨same, size⟩
    unfold runtime.compiler.initialize.lower_loop0.body
    dsimp only at *
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.globals, bind_ok]
    split
    · rename_i more
      have inbounds : index.val < current.module.env.globals.val.length := by
        simpa [UScalar.lt_equiv, Slice.len, alloc.vec.Vec.len, alloc.vec.Vec.deref] using more
      have originalBound : index.val < m.module.env.globals.val.length := by simpa [same] using inbounds
      cases result with
      | Err error => simp [core.result.Result.is_ok, same]; omega
      | Ok value =>
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with initializer_global_total ops law current b index inbounds (by omega)
          as ⟨status, next, b1, source, growth⟩
        step as ⟨nextIndex, increment⟩
        exact ⟨source.trans same, by scalar_tac, by scalar_tac⟩
    · simp only [WP.spec_ok]
      exact ⟨same, by omega⟩
  · exact ⟨rfl, Nat.le_refl _⟩

@[step] theorem initializer_mapping_loop2_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (i : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (space : initializerSize m + 2 * (m.module.tail.data.val.length - i.val) ≤ Usize.max) :
    runtime.compiler.initialize.lower_loop2 ops m budget i status ⦃ out =>
      out.1.module = m.module ∧
      initializerSize out.1 ≤ initializerSize m + 2 * (m.module.tail.data.val.length - i.val) ⦄ := by
  unfold runtime.compiler.initialize.lower_loop2
  apply loop.spec_decr_nat (fun st => m.module.tail.data.val.length - st.2.2.1.val)
    (fun st => st.1.module = m.module ∧
      initializerSize st.1 + 2 * (m.module.tail.data.val.length - st.2.2.1.val) ≤
        initializerSize m + 2 * (m.module.tail.data.val.length - i.val))
  · rintro ⟨current, b, index, result⟩ ⟨same, size⟩
    unfold runtime.compiler.initialize.lower_loop2.body
    dsimp only at *
    simp only [runtime.compiler.ExecutableModule.tail,
      Itasca.metadata.Module.impl.tail, bind_ok]
    split
    · rename_i more
      have inbounds : index.val < current.module.tail.data.val.length := by
        simpa [UScalar.lt_equiv, Slice.len, alloc.vec.Vec.len, alloc.vec.Vec.deref] using more
      have originalBound : index.val < m.module.tail.data.val.length := by simpa [same] using inbounds
      cases result with
      | Err error => simp [core.result.Result.is_ok, same]; omega
      | Ok value =>
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with initializer_data_offset_total ops law current b index inbounds (by omega)
          as ⟨status, next, b1, source, growth⟩
        step as ⟨nextIndex, increment⟩
        exact ⟨source.trans same, by scalar_tac, by scalar_tac⟩
    · simp only [WP.spec_ok]
      exact ⟨same, by omega⟩
  · exact ⟨rfl, Nat.le_refl _⟩

/-- Exact remaining append allowance for element initializer rows and offsets. -/
def initializerElementCost (elements : List Itasca.metadata.Element) : Nat :=
  (elements.map (fun e => e.init.val.length + 3)).sum

theorem initializer_element_cost_step (elements : List Itasca.metadata.Element)
    (index : Nat) (segment : Itasca.metadata.Element) (found : elements[index]? = some segment) :
    initializerElementCost (elements.drop index) = segment.init.val.length + 3 +
      initializerElementCost (elements.drop (index + 1)) := by
  rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp found).1]
  have element := (List.getElem?_eq_some_iff.mp found).2
  simp [initializerElementCost, element]

@[step] theorem initializer_mapping_loop1_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (i : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (space : initializerSize m + initializerElementCost (m.module.env.elements.val.drop i.val) ≤ Usize.max) :
    runtime.compiler.initialize.lower_loop1 ops m budget i status ⦃ out =>
      out.1.module = m.module ∧
      initializerSize out.1 ≤ initializerSize m + initializerElementCost (m.module.env.elements.val.drop i.val) ⦄ := by
  unfold runtime.compiler.initialize.lower_loop1
  apply loop.spec_decr_nat (fun st => m.module.env.elements.val.length - st.2.2.1.val)
    (fun st => st.1.module = m.module ∧
      initializerSize st.1 + initializerElementCost (m.module.env.elements.val.drop st.2.2.1.val) ≤
        initializerSize m + initializerElementCost (m.module.env.elements.val.drop i.val))
  · rintro ⟨current, b, index, result⟩ ⟨same, size⟩
    unfold runtime.compiler.initialize.lower_loop1.body
    dsimp only at *
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok]
    split
    · rename_i more
      have inbounds : index.val < current.module.env.elements.val.length := by
        simpa [UScalar.lt_equiv, Slice.len, alloc.vec.Vec.len, alloc.vec.Vec.deref] using more
      have originalBound : index.val < m.module.env.elements.val.length := by simpa [same] using inbounds
      let segment := current.module.env.elements.val[index.val]
      have found : current.module.env.elements.val[index.val]? = some segment := List.getElem?_eq_getElem inbounds
      have originalFound : m.module.env.elements.val[index.val]? = some segment := by simpa [same] using found
      have cost := initializer_element_cost_step _ _ _ originalFound
      dsimp only [segment] at cost
      cases result with
      | Err error => simp [core.result.Result.is_ok, same]; omega
      | Ok value =>
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with initializer_element_total ops law current b index segment found (by dsimp only [segment]; omega)
          as ⟨status, next, b1, source, growth⟩
        step as ⟨nextIndex, increment⟩
        refine ⟨source.trans same, ?_, ?_⟩
        · rw [increment]; omega
        · scalar_tac
    · simp only [WP.spec_ok]
      exact ⟨same, by omega⟩
  · exact ⟨rfl, Nat.le_refl _⟩
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
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

@[step] theorem initializer_emit_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (code : alloc.vec.Vec runtime.bytecode.Instr) (instruction : runtime.bytecode.Instr)
    (space : code.val.length < Usize.max) :
    runtime.compiler.initialize.emit ops budget code instruction ⦃ out =>
      out.2.2.val.length ≤ code.val.length + 1 ⦄ := by
  unfold runtime.compiler.initialize.emit
  step with charge_instruction ops budget as ⟨status, nextBudget, _⟩
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    exact initializer_push_total ops law nextBudget code instruction space

/-- All constant forms return normally, including an allocator or instruction
budget rejection after partial emission. Each vector grows by at most one. -/
@[step] theorem initializer_constant_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (expr : Itasca.wasm_types.ConstExpr)
    (ty : Itasca.wasm_types.ValueType) (dst : U32)
    (codeFits : function.code.val.length < Usize.max)
    (poolFits : function.v128_pool.val.length < Usize.max) :
    runtime.compiler.initialize.constant ops budget function expr ty dst ⦃ out =>
      out.2.2.code.val.length ≤ function.code.val.length + 1 ∧
      out.2.2.v128_pool.val.length ≤ function.v128_pool.val.length + 1 ∧
      out.2.2.indirect = function.indirect ⦄ := by
  cases expr <;> unfold runtime.compiler.initialize.constant
  all_goals repeat' first
    | (step with initializer_emit_total ops law _ _ _ (by scalar_tac))
    | (step with initializer_push_total ops law _ _ _ (by scalar_tac))
    | simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, WP.spec_ok]
    | split
    | step
    | (apply And.intro)
    | assumption
    | rfl
    | omega

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
  unfold runtime.compiler.initialize.emit_element
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok]
  step
  · simpa [alloc.vec.Vec.deref] using bound
  repeat' first
    | (step with initializer_constant_total ops law _ _ _ _ _ (by scalar_tac) (by scalar_tac))
    | (step with initializer_emit_total ops law _ _ _ (by scalar_tac))
    | (step with initializer_push_total ops law _ _ _ (by scalar_tac))
    | simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, WP.spec_ok]
    | split
    | step
    | (apply And.intro)
    | assumption
    | rfl
    | scalar_tac

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
  unfold runtime.compiler.initialize.emit_data
  simp only [runtime.compiler.ExecutableModule.tail,
    Itasca.metadata.Module.impl.tail, bind_ok]
  step
  repeat' first
    | (step with initializer_constant_total ops law _ _ _ _ _ (by scalar_tac) (by scalar_tac))
    | (step with initializer_emit_total ops law _ _ _ (by scalar_tac))
    | simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, WP.spec_ok]
    | split
    | step
    | (apply And.intro)
    | assumption
    | rfl
    | scalar_tac
end Itasca.Runtime.Compiler

end

/-! ## Initializer Total Segments -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000

@[step] theorem initializer_segment_loop3_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction)
    (i : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (codeFits : function.code.val.length + 5 * (m.module.env.elements.val.length - i.val) ≤ Usize.max)
    (poolFits : function.v128_pool.val.length + (m.module.env.elements.val.length - i.val) ≤ Usize.max)
    (pairFits : function.indirect.val.length + (m.module.env.elements.val.length - i.val) ≤ Usize.max)
    :
    runtime.compiler.initialize.lower_loop3 ops m budget i status function ⦃ out =>
      out.2.2.code.val.length ≤ function.code.val.length + 5 * (m.module.env.elements.val.length - i.val) ∧
      out.2.2.v128_pool.val.length ≤ function.v128_pool.val.length + (m.module.env.elements.val.length - i.val) ∧
      out.2.2.indirect.val.length ≤ function.indirect.val.length + (m.module.env.elements.val.length - i.val) ⦄ := by
  unfold runtime.compiler.initialize.lower_loop3
  apply loop.spec_decr_nat (fun st => m.module.env.elements.val.length - st.2.1.val)
    (fun st => st.2.2.2.code.val.length + 5 * (m.module.env.elements.val.length - st.2.1.val) ≤
        function.code.val.length + 5 * (m.module.env.elements.val.length - i.val) ∧
      st.2.2.2.v128_pool.val.length + (m.module.env.elements.val.length - st.2.1.val) ≤
        function.v128_pool.val.length + (m.module.env.elements.val.length - i.val) ∧
      st.2.2.2.indirect.val.length + (m.module.env.elements.val.length - st.2.1.val) ≤ function.indirect.val.length + (m.module.env.elements.val.length - i.val))
  · rintro ⟨b, index, result, current⟩ ⟨code, pool, pairs⟩
    unfold runtime.compiler.initialize.lower_loop3.body
    dsimp only at *
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok]
    split
    · rename_i more
      have inbounds : index.val < m.module.env.elements.val.length := by
        simpa [UScalar.lt_equiv, Slice.len, alloc.vec.Vec.len, alloc.vec.Vec.deref] using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨by omega, by omega, by omega⟩
      | Ok value =>
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with initializer_emit_element_total ops law m b current index inbounds
          (by omega) (by omega) (by omega) as ⟨status, b1, next, codeGrowth, poolGrowth, pairGrowth⟩
        step as ⟨nextIndex, increment⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · scalar_tac
        · scalar_tac
        · scalar_tac
        · scalar_tac
    · simp only [WP.spec_ok]
      exact ⟨by omega, by omega, by omega⟩
  · exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

@[step] theorem initializer_segment_loop4_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction)
    (i : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (codeFits : function.code.val.length + 5 * (m.module.tail.data.val.length - i.val) ≤ Usize.max)
    (poolFits : function.v128_pool.val.length + (m.module.tail.data.val.length - i.val) ≤ Usize.max)
    :
    runtime.compiler.initialize.lower_loop4 ops m budget i status function ⦃ out =>
      out.2.2.code.val.length ≤ function.code.val.length + 5 * (m.module.tail.data.val.length - i.val) ∧
      out.2.2.v128_pool.val.length ≤ function.v128_pool.val.length + (m.module.tail.data.val.length - i.val) ∧
      out.2.2.indirect = function.indirect ⦄ := by
  unfold runtime.compiler.initialize.lower_loop4
  apply loop.spec_decr_nat (fun st => m.module.tail.data.val.length - st.2.1.val)
    (fun st => st.2.2.2.code.val.length + 5 * (m.module.tail.data.val.length - st.2.1.val) ≤
        function.code.val.length + 5 * (m.module.tail.data.val.length - i.val) ∧
      st.2.2.2.v128_pool.val.length + (m.module.tail.data.val.length - st.2.1.val) ≤
        function.v128_pool.val.length + (m.module.tail.data.val.length - i.val) ∧
      st.2.2.2.indirect = function.indirect)
  · rintro ⟨b, index, result, current⟩ ⟨code, pool, pairs⟩
    unfold runtime.compiler.initialize.lower_loop4.body
    dsimp only at *
    simp only [runtime.compiler.ExecutableModule.tail,
      Itasca.metadata.Module.impl.tail, bind_ok]
    split
    · rename_i more
      have inbounds : index.val < m.module.tail.data.val.length := by scalar_tac
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨by omega, by omega, pairs⟩
      | Ok value =>
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with initializer_emit_data_total ops law m b current index inbounds
          (by omega) (by omega)  as ⟨status, b1, next, codeGrowth, poolGrowth, pairGrowth⟩
        step as ⟨nextIndex, increment⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · scalar_tac
        · scalar_tac
        · exact pairGrowth.trans pairs
        · scalar_tac
    · simp only [WP.spec_ok]
      exact ⟨by omega, by omega, pairs⟩
  · exact ⟨Nat.le_refl _, Nat.le_refl _, rfl⟩
end Itasca.Runtime.Compiler

end

/-! ## Initializer Total -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

/-- A source-derived upper bound on all retained initializer-map appends. -/
def initializerMappingCost (source : Itasca.metadata.Module) : Nat :=
  2 * source.env.globals.val.length + initializerElementCost source.env.elements.val +
  2 * source.tail.data.val.length

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
  let seed := { initializerSeed .I32 with slot_count := 0#u32 }
  have seedEq : runtime.bytecode.CompiledFunction.synthetic (alloc.vec.Vec.new _) 0#u32 = .ok seed := rfl
  unfold runtime.compiler.initialize.lower
  step with initializer_mapping_loop0_total ops law m budget 0#usize (.Ok ())
    (by simp only [initializerMappingCost] at mapSpace; simp; omega)
    as ⟨m1, b1, status, source1, size1⟩
  simp only [show (0#usize).val = 0 from rfl, Nat.sub_zero] at size1
  cases status with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, source1]
    unfold initializerMappingCost; omega
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with initializer_mapping_loop1_total ops law m1 b1 0#usize (.Ok value)
      (by simp only [show (0#usize).val = 0 from rfl, List.drop_zero, source1]; unfold initializerMappingCost at mapSpace; omega)
      as ⟨m2, b2, status, source2, size2⟩
    have same2 : m2.module = m.module := source2.trans source1
    simp only [show (0#usize).val = 0 from rfl, List.drop_zero, source1] at size2
    cases status with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, same2]
      unfold initializerMappingCost; omega
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with initializer_mapping_loop2_total ops law m2 b2 0#usize (.Ok value)
        (by simp only [show (0#usize).val = 0 from rfl, Nat.sub_zero, same2]; unfold initializerMappingCost at mapSpace; omega)
        as ⟨m3, b3, status, source3, size3⟩
      have same3 : m3.module = m.module := source3.trans same2
      simp only [show (0#usize).val = 0 from rfl, Nat.sub_zero, same2] at size3
      have sizeBound : initializerSize m3 ≤ initializerSize m + initializerMappingCost m.module := by
        unfold initializerMappingCost; omega
      cases status with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, same3]
        omega
      | Ok value =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        rw [seedEq, bind_ok]
        step with initializer_segment_loop3_total ops law m3 b3 seed 0#usize (.Ok value)
          (by simp [seed, initializerSeed, same3] <;> omega) (by simp [seed, initializerSeed, same3] <;> omega) (by simp [seed, initializerSeed, same3] <;> omega)
          as ⟨b4, status, function1, code1, pool1, pairs1⟩
        simp [seed, initializerSeed, same3] at code1 pool1 pairs1
        cases status with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, same3]
          omega
        | Ok value =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          step with initializer_segment_loop4_total ops law m3 b4 function1 0#usize (.Ok value)
            (by simp only [show (0#usize).val = 0 from rfl, Nat.sub_zero, same3]; omega)
            (by simp only [show (0#usize).val = 0 from rfl, Nat.sub_zero, same3]; omega)
            as ⟨b5, status, function2, code2, pool2, pairs2⟩
          simp only [show (0#usize).val = 0 from rfl, Nat.sub_zero, same3] at code2
          cases status with
          | Err error =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, same3]
            omega
          | Ok value =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            step with initializer_emit_total ops law b5 function2.code _ (by omega)
              as ⟨status, b6, finalCode, codeCount⟩
            cases status with
            | Err error =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, same3]
              omega
            | Ok value =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
              step with well_formed_total { function2 with code := finalCode } as ⟨valid⟩
              cases valid with
              | false => simp [same3]; omega
              | true =>
                simp only [↓reduceIte]
                step with initializer_push_total ops law b6 m3.functions _
                  (by unfold initializerSize at sizeBound mapSpace; omega)
                  as ⟨status, b7, functions, count⟩
                exact ⟨same3, by unfold initializerSize at *; dsimp at *; omega⟩

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
