import Itasca.Runtime.Compiler.Module.InitializerTotal
import Itasca.Runtime.Compiler.Local.Capacity.GlobalAvailability
import Itasca.Module.Elab.TypingInversion
import Itasca.Runtime.Compiler.Module.CodeRegionComplete
import Itasca.Runtime.Compiler.Module.CompileSubmit
import Itasca.Runtime.Compiler.Local.Relations.Layout.LayoutProofs
import Itasca.Stream.DriverRegions
import Itasca.Runtime.Compiler.Body.Relations.Entry.PreparedRawInitial
import Itasca.Runtime.Compiler.Body.Relations.Table.PreparedTableInitial
import Itasca.Runtime.Compiler.Body.Relations.Executable.RecordingEmission
import Itasca.Runtime.Compiler.Body.Relations.Replay.ReachedBodySafetyWasm2
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post

/-!
Sections, each formerly its own module: InitializerSourceTotal, SubmitTotal, SchedulerSubmissionSafety, CompileTotalDriver, SchedulerProfileSafety, CompileProfileTotal, PreparedExecutableSafety, CompileTotal.
-/

/-! ## InitializerSourceTotal -/

section

/-!
Independent source bounds and normal return of source initializer lowering.
-/

/-! ## Initializer Source Bounds -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ModuleBinary

/-- The fixed module header fits the compiler's intrinsic input bound. -/
theorem module_header_fits : magicVersion.length ≤ Itasca.limits.MAX_MODULE_BYTES.val := by
  simp only [magicVersion, List.length_cons, List.length_nil, Nat.reduceAdd,
    Itasca.limits.MAX_MODULE_BYTES, UScalar.ofNatCore_val_eq, Nat.reduceLeDiff]

private theorem leb_nonempty {bytes value} (h : Itasca.Leb128.Encoding bytes value) :
    1 ≤ bytes.length := by
  obtain ⟨before, last, rfl, _⟩ := h
  simp

private theorem const_nonempty {value bytes} (h : ConstEncoding value bytes) :
    1 ≤ bytes.length := by
  cases h <;> simp

private theorem rep_count {α : Type} {R : α → List U8 → Prop} {values bytes}
    (h : Rep R values bytes) (positive : ∀ value bytes, R value bytes → 1 ≤ bytes.length) :
    values.length ≤ bytes.length := by
  induction h with
  | nil => simp
  | cons hx _ ih =>
    have := positive _ _ hx
    simp only [List.length_cons, List.length_append]
    omega

private theorem vec_count {α : Type} {R : α → List U8 → Prop} {values bytes}
    (h : VecEncoding R values bytes) (positive : ∀ value bytes, R value bytes → 1 ≤ bytes.length) :
    values.length + 1 ≤ bytes.length := by
  obtain ⟨count, entries, hc, hr, rfl⟩ := h
  have := leb_nonempty hc
  have := rep_count hr positive
  simp only [List.length_append]
  omega

private theorem element_cost {entry bytes}
    (h : ElementEncodingFor entry bytes) : entry.init.length + 3 ≤ 3 * bytes.length := by
  cases h with
  | activeIndices _ _ he | passiveIndices _ he | explicitIndices _ _ _ he | declarativeIndices _ he =>
    have := vec_count he (fun _ _ h => leb_nonempty h)
    simp only [List.length_map, List.length_append, List.length_singleton]
    omega
  | activeExpressions _ _ he | passiveExpressions _ he | explicitExpressions _ _ _ he | declarativeExpressions _ he =>
    have := vec_count he (fun _ _ h => const_nonempty h)
    simp only [List.length_append, List.length_singleton]
    omega

private theorem global_cost {entry bytes} (h : GlobalEncoding entry bytes) : 2 ≤ 3 * bytes.length := by
  obtain ⟨ty, expr, rfl, _, rfl⟩ := h
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

private theorem data_cost {entry bytes}
    (h : DataEncodingFor entry bytes) : 2 ≤ 3 * bytes.length := by
  have vec_positive {α : Type} {R : α → List U8 → Prop} {values bytes}
      (h : VecEncoding R values bytes) : 1 ≤ bytes.length := by
    obtain ⟨count, entries, hc, _, rfl⟩ := h
    have := leb_nonempty hc
    simp only [List.length_append]
    omega
  cases h with
  | active _ _ he | passive _ he =>
    have := vec_positive he
    simp only [List.length_append]
    omega

private theorem rep_cost {α : Type} {R : α → List U8 → Prop} {values bytes}
    (cost : α → Nat) (h : Rep R values bytes)
    (bounded : ∀ value bytes, R value bytes → cost value ≤ 3 * bytes.length) :
    (values.map cost).sum ≤ 3 * bytes.length := by
  induction h with
  | nil => simp
  | cons hx _ ih =>
    have := bounded _ _ hx
    simp only [List.map_cons, List.sum_cons, List.length_append]
    omega

private theorem padded_cost {α : Type} {R : α → List U8 → Prop} {id values bytes}
    (cost : α → Nat) (h : PaddedEncoding id (VecEncoding R) [] values bytes)
    (bounded : ∀ value bytes, R value bytes → cost value ≤ 3 * bytes.length) :
    (values.map cost).sum ≤ 3 * bytes.length := by
  obtain ⟨customs, sec, _, hs, rfl⟩ := h
  cases hs with
  | absent => simp
  | present hp =>
    obtain ⟨size, payload, _, ⟨count, entries, _, hr, rfl⟩, rfl⟩ := hp
    have := rep_cost cost hr bounded
    simp only [List.length_append, List.length_cons]
    omega

/-- The independently encoded declaration sections pay for all initializer-map
appends and the defined functions, including empty element segments. -/
theorem initializer_cost_bytes {R raw bytes}
    (encoding : ModuleEncodingWith R raw bytes) :
    raw.functions.length + 2 * raw.globals.length +
      (raw.elements.map (fun e => e.init.length + 3)).sum + 2 * raw.data.length ≤
      3 * bytes.length := by
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
    codes, datas, customs, _, _, hf, _, _, hg, _, _, he, _, _, hd, _, rfl, _⟩ := encoding
  have hf := padded_cost (fun _ => 1) hf (fun _ _ h => by have := leb_nonempty h; omega)
  have hg := padded_cost (fun _ => 2) hg (fun _ _ h => global_cost h)
  have he := padded_cost (fun e => e.init.length + 3) he (fun _ _ h => element_cost h)
  have hd := padded_cost (fun _ => 2) hd (fun _ _ h => data_cost h)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one] at hf hg hd
  simp only [List.length_append]
  omega

/-- Canonical metadata and the fixed module-byte cap discharge both numeric
headroom obligations before initializer lowering runs. No successful initializer
result is assumed. -/
theorem initializer_source_headroom {R raw bytes env tail}
    (encoding : ModuleEncodingWith R raw bytes)
    (matched : Itasca.ModuleElaboration.Matches env tail raw)
    (bounded : bytes.length ≤ Itasca.limits.MAX_MODULE_BYTES.val) :
    env.func_type_indices.val.length + initializerMappingCost ⟨env, tail⟩ + 1 ≤ Usize.max ∧
    5 * (env.elements.val.length + tail.data.val.length) + 1 ≤ Usize.max := by
  have cost := initializer_cost_bytes encoding
  have segments := segment_count_bytes encoding
  have costEq := congrArg (fun raw : Module => raw.functions.length + 2 * raw.globals.length +
    (raw.elements.map (fun e => e.init.length + 3)).sum + 2 * raw.data.length) matched.1
  have segmentEq := congrArg (fun raw : Module => raw.elements.length + raw.data.length) matched.1
  simp only [Itasca.ModuleElaboration.fromEnv, List.length_map, List.map_map,
    Function.comp_def, Itasca.ModuleEnv.rawElement] at costEq segmentEq
  rw [costEq] at cost
  rw [segmentEq] at segments
  have wordBound : U32.max ≤ Usize.max := by scalar_tac
  norm_num [Itasca.limits.MAX_MODULE_BYTES, U32.max_eq] at bounded wordBound
  dsimp only [initializerMappingCost, initializerElementCost]
  constructor <;> omega

end Itasca.Runtime.Compiler

end

/-! ## Initializer Source Total -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ModuleBinary

/-- The actual fresh compiler-driver input has enough space for initializer
lowering, directly from the independently encoded module and collected function
count. This covers successful lowering and every normal error result. -/
theorem initializer_lower_source_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (env : Itasca.metadata.Env) (tail : Itasca.metadata.Tail)
     (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction)
    (budget : runtime.compiler.Budget A) {R raw bytes}
    (encoding : ModuleEncodingWith R raw bytes)
    (matched : Itasca.ModuleElaboration.Matches env tail raw)
    (bounded : bytes.length ≤ Itasca.limits.MAX_MODULE_BYTES.val)
    (functionCount : functions.val.length = env.func_type_indices.val.length) :
    runtime.compiler.initialize.lower ops (uninitializedModule env tail functions) budget
      ⦃ _ => True ⦄ := by
  obtain ⟨mapSpace, segmentSpace⟩ := initializer_source_headroom encoding matched bounded
  apply initializer_lower_fresh_total ops law _ budget rfl rfl rfl rfl
  · simpa only [uninitializedModule, functionCount] using mapSpace
  · exact segmentSpace

end Itasca.Runtime.Compiler

end

end

/-! ## SubmitTotal -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
open runtime.compiler

/-- The eager submission loop requires entry termination only at reached
scheduler/worker pairs. An ordinary entry error immediately ends the loop. -/
theorem compiler_submit_loop_total_on {A : Type} (ops : runtime.platform.Alloc A)
    (safe : CompileScheduler A → stream.CodeBatch → Prop)
    (entries : ∀ scheduler worker, safe scheduler worker →
      CompileScheduler.compile_entry ops scheduler worker ⦃ out =>
        out.1 = .Ok () → safe out.2.1 out.2.2 ⦄)
    (scheduler : CompileScheduler A) (worker : stream.CodeBatch)
    (index : Usize) (status : core.result.Result Unit error.Error)
    (held : status = .Ok () → safe scheduler worker) :
    CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop
      ops scheduler worker index status ⦃ out =>
        ∃ final batch result, out = submitPack final batch result ∧
          (result = .Ok () → safe final batch) ⦄ := by
  unfold CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop
  apply loop.spec_decr_nat (fun st => Usize.max - st.2.2.1.val)
    (fun st => st.2.2.2 = .Ok () → safe st.1 st.2.1)
  · rintro ⟨scheduler,worker,index,status⟩ held
    simp only [CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop.body,Itasca.stream.CodeBatch.len,bind_ok]
    split
    · rename_i inbounds
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok,bind_ok,Bool.false_eq_true,↓reduceIte,WP.spec_ok]
        exact ⟨scheduler,worker,.Err error,rfl,by intro h; cases h⟩
      | Ok result =>
        cases result
        simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
        obtain ⟨⟨result,next,batch⟩,run,preserved⟩ := WP.spec_imp_exists (entries scheduler worker (held rfl))
        rw [run]
        simp only [bind_ok]
        step
        exact ⟨preserved,by scalar_tac⟩
    · simp only [WP.spec_ok]
      exact ⟨scheduler,worker,status,rfl,held⟩
  · exact held

/-- Queue publication is safe once reached entry states provide bounded queue
headroom. The successful entry invariant is not required after a rejection. -/
theorem compiler_submit_total_on {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (safe : CompileScheduler A → stream.CodeBatch → Prop)
    (entries : ∀ scheduler worker, safe scheduler worker →
      CompileScheduler.compile_entry ops scheduler worker ⦃ out =>
        out.1 = .Ok () → safe out.2.1 out.2.2 ⦄)
    (room : ∀ scheduler worker, safe scheduler worker → scheduler.completed.val.length < Usize.max)
    (scheduler : CompileScheduler A) (worker : stream.CodeBatch)
    (held : safe scheduler worker) :
    CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch ops scheduler worker
      ⦃ _ => True ⦄ := by
  obtain ⟨out,run,final,batch,result,rfl,preserved⟩ := WP.spec_imp_exists
    (compiler_submit_loop_total_on ops safe entries scheduler worker 0#usize (.Ok ()) (fun _ => held))
  unfold CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch
  rw [run]
  simp only [submitPack,bind_ok,uncurry_apply_pair]
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok accepted =>
    cases accepted
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    obtain ⟨⟨result,budget,queue⟩,pushed,_⟩ := WP.spec_imp_exists
      (budget_push ops law final.budget final.completed batch (room final batch (preserved rfl)))
    rw [pushed]
    cases result <;> simp [visitor_result,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca.Runtime.Compiler

end

/-! ## SchedulerSubmissionSafety -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
open runtime.compiler

theorem CompileEntryWitness.scheduler_ready {A : Type} {ops : runtime.platform.Alloc A}
    {before after : CompileScheduler A} {worker finalWorker : stream.CodeBatch}
    (entry : CompileEntryWitness ops before after worker finalWorker)
    {env : metadata.Env} {cursor : Nat} (ready : SchedulerReady env cursor before) :
    SchedulerReady env cursor after := by
  rw [entry.published]
  refine ⟨ready.signatures,ready.functionSlots,?_,ready.origin,ready.queue,ready.cursorBound⟩
  simpa only [alloc.vec.Vec.set_val_eq,List.length_set] using ready.functions

/-- The queue's headroom follows the issued cursor, rather than a separate
allocator assumption. Entry termination is required only for this batch's
actual dispatch/validation successors. -/
theorem compiler_submit_safety {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (env : metadata.Env)
    (issued : StreamBatch.Issued) (sameEnv : issued.env = env) (bounded : issued.Bounded)
    (scheduler : CompileScheduler A) (ready : SchedulerReady env issued.first_func.val scheduler)
    (entries : ∀ current worker, SchedulerReady env issued.first_func.val current →
      StreamBatch.Reachable issued worker → CompileScheduler.compile_entry ops current worker ⦃ _ => True ⦄) :
    CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch ops scheduler issued.seed ⦃ out =>
      out.1 = .Ok () → SchedulerReady env (issued.first_func.val + issued.num_funcs.val) out.2 ⦄ := by
  let safe := fun (current : CompileScheduler A) (worker : stream.CodeBatch) => SchedulerReady env issued.first_func.val current ∧
    StreamBatch.Reachable issued worker
  have entrySafe : ∀ current worker, safe current worker →
      CompileScheduler.compile_entry ops current worker ⦃ out => out.1 = .Ok () → safe out.2.1 out.2.2 ⦄ := by
    intro current worker held
    obtain ⟨⟨status,after,batch⟩,run,_⟩ := WP.spec_imp_exists (entries current worker held.1 held.2)
    rw [run]
    apply (WP.spec_ok _).mpr
    intro accepted
    dsimp only at accepted
    obtain ⟨w⟩ := compile_entry_accepted ops current after worker batch (by simpa only [accepted] using run)
    exact ⟨w.scheduler_ready held.1,w.reachable held.2⟩
  have room : ∀ current worker, safe current worker → current.completed.val.length < Usize.max := by
    intro current worker held
    have count := bounded.1
    have extent := bounded.2.1
    rw [sameEnv] at extent
    have queue := held.1.queue
    have max := env.func_type_indices.property
    omega
  obtain ⟨⟨status,after⟩,run,_⟩ := WP.spec_imp_exists
    (compiler_submit_total_on ops law safe entrySafe room scheduler issued.seed ⟨ready,.seed⟩)
  rw [run]
  apply (WP.spec_ok _).mpr
  intro accepted
  dsimp only at accepted
  obtain ⟨middle,worker,compiled,queue,updated⟩ := compiler_submit_accepted ops law scheduler after issued.seed
    (by simpa only [accepted] using run)
  have retained := compiled.fold (fun current _ => SchedulerReady env issued.first_func.val current)
    ready (fun _ _ _ _ held w => w.scheduler_ready held)
  have bound : issued.first_func.val + issued.num_funcs.val ≤ env.func_type_indices.val.length := by
    simpa only [sameEnv] using bounded.2.1
  refine ⟨?_,?_,?_,?_,?_,bound⟩
  · rw [updated]
    exact retained.signatures
  · rw [updated]
    exact retained.functionSlots
  · rw [updated]
    exact retained.functions
  · rw [updated]
    exact retained.origin
  · rw [queue,List.length_append,List.length_singleton]
    have := ready.queue
    have := bounded.1
    omega

end Itasca.Runtime.Compiler

end

/-! ## CompileTotalDriver -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
open runtime.compiler

/-- Common driver assembly from the reached streaming phase. This internal
adapter derives source initializer space and all result/error bookkeeping. -/
theorem compile_with_total_of_streaming {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8)
    (limits : CompileLimits)
    (streaming : ∀ (codeStart codeEnd : Usize) (storage : metadata.Env),
      codeStart.val ≤ codeEnd.val ∧ codeEnd.val ≤ bytes.length →
      stream.validate_streaming CompileSource.Insts.ItascaStreamSource
        (CompileScheduler.Insts.ItascaStreamStreamingVisitor ops) 0#u64
        {bytes,code_start := codeStart,code_end := codeEnd}
        (initialScheduler A limits codeStart) storage ⦃ out =>
          out.1 = .Ok () → SchedulerReady out.2.2 out.2.2.func_type_indices.val.length out.2.1 ⦄) :
    runtime.compiler.compile_with ops bytes limits ⦃ _ => True ⦄ := by
  unfold runtime.compiler.compile_with
  dsimp only
  split
  · simp
  · obtain ⟨⟨codeStart,codeEnd⟩,region,bounds⟩ := WP.spec_imp_exists (code_region_spec bytes)
    obtain ⟨storage,initialized,_⟩ := WP.spec_imp_exists metadata.Env.new.spec
    simp only [region,initialized,bind_ok,uncurry_apply_pair]
    obtain ⟨⟨status,scheduler,env⟩,validated,ready⟩ := WP.spec_imp_exists (streaming codeStart codeEnd storage bounds)
    simp only [initialScheduler] at validated
    simp only [validated]
    simp only [bind_ok,uncurry_apply_pair]
    cases status with
    | Err error => cases scheduler.budget.error <;> simp
    | Ok acceptedUnit =>
      cases acceptedUnit
      have held := ready rfl
      cases tailReady : scheduler.tail with
      | none => simp [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | some tail =>
        obtain ⟨raw,encoding,matched,_,bounded⟩ := compiler_stream_source ops law bytes limits
          codeStart codeEnd storage env scheduler tail bounds tailReady validated
        simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
        obtain ⟨⟨collected,budget,pending⟩,collect,order⟩ := WP.spec_imp_exists
          (collect_functions_spec ops law scheduler.budget scheduler.functions)
        rw [collect]
        simp only [bind_ok,uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch]
        cases collected with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok functions =>
          have count : functions.val.length = env.func_type_indices.val.length := by
            have eq := congrArg List.length (order functions rfl)
            simp only [List.length_map] at eq
            exact eq.symm.trans held.functions
          obtain ⟨⟨result,executable,finalBudget⟩,lowered,_⟩ := WP.spec_imp_exists
            (initializer_lower_source_total ops law env tail functions budget encoding matched bounded count)
          simp only [bind_ok]
          simp only [uninitializedModule] at lowered
          rw [lowered]
          cases result <;> cases choice : finalBudget.error <;> simp [choice]

end Itasca.Runtime.Compiler

end

/-! ## SchedulerProfileSafety -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
open runtime.compiler

/-- Signature limits retained from actual environment decoding. -/
def ProfileEnvironment (env : metadata.Env) : Prop :=
  Profile.EnvironmentWithinLimits env

def ReachedProfileEntriesTotal {A : Type} (ops : runtime.platform.Alloc A) : Prop :=
  ∀ (env : metadata.Env) (issued : StreamBatch.Issued) (scheduler : CompileScheduler A)
    (worker : stream.CodeBatch), issued.env = env → issued.Bounded → CodeEntry.Bounds env →
    ProfileEnvironment env →
    SchedulerReady env issued.first_func.val scheduler →
    StreamBatch.Reachable issued worker → CompileScheduler.compile_entry ops scheduler worker ⦃ _ => True ⦄

theorem compiler_scheduler_profile_callbacks_on {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (entries : ReachedProfileEntriesTotal ops) :
    StreamScheduler.CallbacksOn (CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      SchedulerInitial (fun env cursor scheduler => SchedulerReady env cursor scheduler ∧ ProfileEnvironment env)
      (ProfileEnvironment) := by
  constructor
  · intro scheduler chunk
    exact ⟨(.Ok (),scheduler),rfl⟩
  · intro before chunk after accepted held
    have same : before = after := by simpa [CompileScheduler.Insts.ItascaStreamStreamingVisitor,
      CompileScheduler.Insts.ItascaMetadataModuleVisitor,
      CompileScheduler.Insts.ItascaMetadataModuleVisitor.on_custom_section] using accepted
    simpa only [same] using held
  · intro env cursor before chunk after accepted held
    have same : before = after := by simpa [CompileScheduler.Insts.ItascaStreamStreamingVisitor,
      CompileScheduler.Insts.ItascaMetadataModuleVisitor,
      CompileScheduler.Insts.ItascaMetadataModuleVisitor.on_custom_section] using accepted
    simpa only [same] using held
  · intro scheduler region held
    simpa [CompileScheduler.Insts.ItascaStreamStreamingVisitor,
      CompileScheduler.Insts.ItascaStreamStreamingVisitor.custom_region] using held
  · intro env cursor scheduler region held
    simpa [CompileScheduler.Insts.ItascaStreamStreamingVisitor,
      CompileScheduler.Insts.ItascaStreamStreamingVisitor.custom_region] using held
  · intro scheduler env held admitted bounds
    apply WP.spec_mono (compiler_environment_safety ops law scheduler env held)
    intro out fresh config accepted
    exact ⟨fresh config accepted,admitted⟩
  · intro env
    constructor
    · intro scheduler issued held sameEnv bounded bounds
      apply WP.spec_mono (compiler_submit_safety ops law env issued sameEnv bounded scheduler held.1
        (fun current worker ready reached => entries env issued current worker sameEnv bounded
          (by simpa only [sameEnv] using bounds) held.2 ready reached))
      intro out fresh accepted
      exact ⟨fresh accepted,held.2⟩
    · intro cursor scheduler held
      apply WP.spec_mono (compiler_poll_safety ops env cursor scheduler held.1)
      intro out fresh batch accepted
      exact ⟨fresh batch accepted,held.2⟩
  · intro env scheduler held
    simpa [CompileScheduler.Insts.ItascaStreamStreamingVisitor,
      CompileScheduler.Insts.ItascaStreamStreamingVisitor.code_end] using held
  · intro env scheduler tail held
    simp only [CompileScheduler.Insts.ItascaStreamStreamingVisitor,
      CompileScheduler.Insts.ItascaStreamStreamingVisitor.tail_ready,WP.spec_ok]
    intro _
    exact ⟨⟨held.1.signatures,held.1.functionSlots,held.1.functions,held.1.origin,held.1.queue,held.1.cursorBound⟩,held.2⟩

/-- Actual environment decoding supplies the signature limits before any
worker is issued. It is retained through every reached scheduler state. -/
theorem compiler_stream_spec_of_profile_entries {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (entries : ReachedProfileEntriesTotal ops) (source : CompileSource)
    (sourceBounds : SourceBounds source) (scheduler : CompileScheduler A)
    (initial : SchedulerInitial scheduler) (storage : metadata.Env) :
    stream.validate_streaming CompileSource.Insts.ItascaStreamSource
      (CompileScheduler.Insts.ItascaStreamStreamingVisitor ops) 0#u64 source scheduler storage ⦃ out =>
        out.1 = .Ok () → SchedulerReady out.2.2 out.2.2.func_type_indices.val.length out.2.1 ⦄ := by
  apply WP.spec_mono (stream.validate_streaming.spec_on CompileSource.Insts.ItascaStreamSource
    (CompileScheduler.Insts.ItascaStreamStreamingVisitor ops) 0#u64 source scheduler storage
    (source_callbacks_total source sourceBounds) SchedulerInitial
    (fun env cursor scheduler => SchedulerReady env cursor scheduler ∧ ProfileEnvironment env)
    (ProfileEnvironment) (compiler_scheduler_profile_callbacks_on ops law entries) initial
    (by intro bytes env next bounded accepted
        exact (ModuleEnv.profile_accepted_entry_conditions bytes env next bounded accepted).2))
  intro out fresh accepted
  exact (fresh accepted).1
end Itasca.Runtime.Compiler

end

/-! ## CompileProfileTotal -/

section

/-!
Normal return of default and explicit-budget compilation, projecting the shared generic compiler totality proof.
-/

/-! ## Compile Default Total -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
open runtime.compiler

@[step] theorem compiler_default_limits_total :
    CompileLimits.Insts.CoreDefaultDefault.default ⦃ _ => True ⦄ := by
  unfold CompileLimits.Insts.CoreDefaultDefault.default
  step
  step

end Itasca.Runtime.Compiler

end

/-! ## Compile Profile Total -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
open runtime.compiler

/-- Internal remaining body obligation, restricted to independently decoded
entry metadata, captured signature tables, and the actual fresh compiler/start
calls. It does not presume a successful body or final compilation. -/
def ProfilePreparedBodiesTotal {A : Type} (ops : runtime.platform.Alloc A) : Prop :=
  ∀ (data : Slice U8) (env : metadata.Env) (index start : Usize)
    (signatures : Slice Signature) (functionSlots : Slice U32) (budget : Budget A)
    (batchStart : Usize) (initial started : FunctionCompiler A)
    (prepared : CodeEntry.Prepared data env index start),
    CodeEntry.Bounds env → ProfileEnvironment env → SignatureSequence signatures.val env.types.val →
    functionSlots.val.map (fun word => word.val) = env.func_types.val.map (fun ty => signatureSlots ty.params.val) →
    batchStart.val + data.length ≤ Usize.max →
    FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial →
    FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start ops initial prepared.ctx
      prepared.typeIdx prepared.bodyStart prepared.finish = .ok (.Ok (),started) →
    code.validate_body_with (FunctionCompiler.Insts.ItascaCodeOpVisitor ops) prepared.body env prepared.ctx
      prepared.typeIdx started ⦃ _ => True ⦄

/-- All entry dispatch, local decoding, start-callback and checker obligations
are discharged; the body proof is used only at the fresh state reached here. -/
theorem compiler_profile_entries_total_of_prepared_bodies {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (bodies : ProfilePreparedBodiesTotal ops) : ReachedProfileEntriesTotal ops := by
  intro env issued scheduler worker sameEnv bounded envBounds admitted held reached
  apply compiler_entry_total_of_validation ops scheduler issued worker bounded reached held.origin
  intro entry dispatched batchStart initial dispatch added created
  have reached' := StreamBatch.Reachable.dispatch reached dispatch
  obtain ⟨_,_,workerEnv,workerCode,workerOffset,workerFirst,workerCount⟩ := reached'.validation.1
  have envEq : dispatched.env = env := workerEnv.trans sameEnv
  have maxRoom : limits.MAX_MODULE_BYTES.val + limits.MAX_MODULE_BYTES.val ≤ Usize.max := by
    simp only [limits.MAX_MODULE_BYTES]
    scalar_tac
  have addFits : scheduler.code_start.val + dispatched.code_offset.val ≤ Usize.max := by
    rw [workerOffset]
    have := bounded.2.2
    have := held.origin
    omega
  have arithmetic := Usize.add_spec (x := scheduler.code_start) (y := dispatched.code_offset) addFits
  rw [added,WP.spec_ok] at arithmetic
  have sourceFits : batchStart.val + dispatched.code.length ≤ Usize.max := by
    rw [workerCode]
    have bound := bounded.2.2
    have origin := held.origin
    rw [workerOffset] at arithmetic
    omega
  have range : dispatched.first_func.val + dispatched.num_funcs.val ≤ dispatched.env.func_type_indices.val.length := by
    simpa only [workerFirst,workerCount,workerEnv] using bounded.2.1
  apply Itasca.stream.CodeBatch.validate_func.prepared_total _ dispatched entry.index initial
    (by simpa only [envEq] using envBounds) range
  · intro prepared
    exact prepared_compiler_start_total ops law prepared
      (by simpa [alloc.vec.Vec.deref,envEq] using held.signatures)
      (by have bound := prepared.body_bytes.bound; omega) created
  · intro prepared started startedCall
    have localBodies := bodies
    exact localBodies dispatched.code dispatched.env entry.index dispatched.validated_end
      (alloc.vec.Vec.deref scheduler.signatures) (alloc.vec.Vec.deref scheduler.func_param_slots)
      {scheduler.budget with marker := ()} batchStart initial started prepared
      (by simpa only [envEq] using envBounds)
      (by simpa only [envEq] using admitted)
      (by simpa [alloc.vec.Vec.deref,envEq] using held.signatures)
      (by simpa [alloc.vec.Vec.deref,envEq] using held.functionSlots) sourceFits created startedCall


/-- Driver normality with the signature limits supplied by actual environment
validation. No restriction on the input bytes is required. -/
theorem compile_with_total_of_profile_entries {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8)
    (limits : CompileLimits) (entries : ReachedProfileEntriesTotal ops) :
    runtime.compiler.compile_with ops bytes limits ⦃ _ => True ⦄ := by
  apply compile_with_total_of_streaming ops law bytes limits
  intro codeStart codeEnd storage bounds
  by_cases small : codeStart.val ≤ Itasca.limits.MAX_MODULE_BYTES.val
  · exact compiler_stream_spec_of_profile_entries ops law entries
      {bytes,code_start := codeStart,code_end := codeEnd} bounds _
      ⟨rfl,rfl,rfl,rfl,small⟩ storage
  · rw [compiler_stream_large_environment _
      {bytes,code_start := codeStart,code_end := codeEnd} bounds
      (by change Itasca.limits.MAX_MODULE_BYTES.val < codeStart.val; omega)]
    simp

/-- The complete driver reduces to body normality at valid, actually
prepared function entries. Header, local, initializer and checker paths are derived. -/
theorem compile_with_total_of_profile_prepared_bodies {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8)
    (limits : CompileLimits) (bodies : ProfilePreparedBodiesTotal ops) :
    runtime.compiler.compile_with ops bytes limits ⦃ _ => True ⦄ :=
  compile_with_total_of_profile_entries ops law bytes limits
    (compiler_profile_entries_total_of_prepared_bodies ops law bodies)
end Itasca.Runtime.Compiler

end

end

/-! ## PreparedExecutableSafety -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual entry setup supplies every static and allocation ledger field needed
by the reached-body normality proof, before reading any instruction. -/
theorem prepared_executable_safety_wasm2 {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial started : runtime.compiler.FunctionCompiler A} {data env index start}
    (w : CodeEntry.Prepared data env index start)
    (small : w.body.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (signaturesMatch : SignatureSequence signatures.val env.types.val)
    (slotsMatch : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ty => signatureSlots ty.params.val))
    (batchBound : batchStart.val + data.length ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (begun : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial w.ctx w.typeIdx w.bodyStart w.finish = .ok (.Ok (),started)) :
    let C := EnvTranslation.context env w.ctx
    CompilerEntryFacts started env w.ctx w.typeIdx w.ft w.body ∧
    EnvTranslation.Matches env ⟨w.ctx.locals,w.ft.results⟩ C ∧
    IndexedTableReaderCompilerPointWasm2 (fun tables => ExecutableEmission tables C) started started
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (w.ft.results.val.map Translate.valueType) (w.ctx.locals.val.map Translate.valueType)
      w.body env w.ctx.locals w.typeIdx w.ft (Wasm2.initial w.typeIdx) ∧
    ObservedStack started [] ∧
    started.function.indirect.val.length ≤ started.function.code.val.length ∧
    started.function.simd.val.length ≤ started.function.code.val.length ∧
    started.function.v128_pool.val.length ≤ started.function.code.val.length ∧
    FixupBudget started.frames.val started.function.code.val.length := by
  have endFits : batchStart.val + w.finish.val ≤ Usize.max := by
    have bound := w.body_bytes.bound
    omega
  obtain ⟨facts,point⟩ := indexed_table_prepared_compiler_initial_wasm2
    (fun tables => ExecutableEmission tables (EnvTranslation.context env w.ctx))
    ops law w small signaturesMatch slotsMatch endFits created begun
  refine ⟨facts,?_,point,prepared_compiler_raw_initial ops law w signaturesMatch endFits created begun⟩
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  simp only [EnvTranslation.context,w.context_results]

end Itasca.Runtime.Compiler

end

/-! ## CompileTotal -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual prepared function bodies return normally for WebAssembly Core 2.0,
without a body-acceptance or callback-correctness premise. The initial source
and allocation invariants come from actual entry setup. -/
theorem profile_prepared_bodies_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) :
    ProfilePreparedBodiesTotal ops := by
  intro data env index start signatures functionSlots budget batchStart initial started prepared
    bounds environment signaturesMatch slotsMatch batchBound created begun
  by_cases small : prepared.body.length ≤ limits.MAX_FUNCTION_BYTES.val
  · obtain ⟨facts,matched,point,observed,indirect,simd,pool,fixups⟩ :=
      prepared_executable_safety_wasm2 ops law prepared small signaturesMatch slotsMatch batchBound created begun
    have contextEq : prepared.ctx = ⟨prepared.ctx.locals,prepared.ft.results⟩ := by
      have results : prepared.ctx.results = prepared.ft.results :=
        alloc.vec.Vec.ext _ _ prepared.context_results
      cases h : prepared.ctx
      simp_all
    have body := compiler_body_wasm2_total ops law started (EnvTranslation.context env prepared.ctx)
      (prepared.ctx.locals.val.map Translate.valueType) prepared.body env prepared.ctx.locals prepared.typeIdx prepared.ft
      point facts.localLayout facts.locals facts.functionSlots matched rfl facts.signatures
      ⟨observed,indirect,simd,pool,fixups⟩ facts.bodyBound
    rw [← contextEq] at body
    obtain ⟨result,run,_⟩ := WP.spec_imp_exists body
    simp [run]
  · rw [reader_body_too_large _ prepared.body env prepared.ctx prepared.typeIdx started (by omega)]
    simp

/-- Complete-module compilation returns success or a reported validation or
resource error on arbitrary bytes and arbitrary compiler limits. -/
@[step] theorem compile_with_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits) :
    runtime.compiler.compile_with ops bytes limits ⦃ _ => True ⦄ :=
  compile_with_total_of_profile_prepared_bodies ops law bytes limits
    (profile_prepared_bodies_total ops law)

end Itasca.Runtime.Compiler

end
