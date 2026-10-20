import Exec.Code.Module.CodeRegionComplete
import Exec.Code.Module.SourceRegionsAvailable
import Exec.Code.Module.StreamingAvailable
import Exec.Code.Module.CollectionAvailable
import Exec.Code.Module.SourceCompilationDemand

namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Independent complete-profile module validity, including intrinsic binary
and signature limits. No compiler run or emitted object occurs in these fields. -/
structure ValidCompilationSource (bytes : Slice U8) (profile : ValidationProfile)
    (raw : ModuleBinary.Module) : Prop where
  encoding : ModuleBinary.ModuleEncodingWithinLimits raw bytes.val profile
  signatures : ModuleBinary.ModuleSignaturesWithinLimits raw profile
  elaborated : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw)
  typed : Module_ok (ModuleElaboration.moduleOf raw)
  restrictions : ModuleElaboration.Profile raw profile

/-- Compiler eligibility is entirely source-facing: configured module size and
independent numerical demand for the canonical source-region metadata. Region
certificates are derived by validator completeness, not assumed compiler output. -/
structure CompileEligible (A : Type) (bytes : Slice U8) (profile : ValidationProfile)
    (raw : ModuleBinary.Module) (limits : runtime.compiler.CompileLimits) (bound : Nat) : Prop where
  moduleBytes : bytes.length ≤ limits.max_module_bytes.val
  demand : ∀ regions env tail, StreamCompleteRegions.Certificate bytes raw regions env tail profile →
    ∃ bodyBytes localCount peak, SourceCompilationDemand A env tail profile limits bodyBytes localCount peak bound

private theorem module_fits (bytes : Slice U8) (limit : Usize) (bounded : bytes.length ≤ limit.val) :
    ¬ Slice.len bytes > limit := by scalar_tac

private theorem certificate_initializer_typing {bytes raw regions env tail profile}
    (certificate : StreamCompleteRegions.Certificate bytes raw regions env tail profile)
    (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction) :
    InitializerSourceTyping (uninitializedModule env tail profile functions) := by
  have environment := Itasca.module.validate_env.profile_semantic_spec regions.env profile
  rw [certificate.environment,WP.spec_ok] at environment
  obtain ⟨_,_,valid,_,_,_⟩ := environment
  have dataValid := Itasca.module.validate_tail.spec regions.tail 0#usize env (by simp) profile
  rw [certificate.tail_accepted,WP.spec_ok] at dataValid
  exact InitializerSourceTyping.of_valid valid dataValid.2.1

/-- Independently valid modules in either complete profile compile successfully
when explicit source-only compiler bounds and bounded allocations are available.
Aeneas normal return and the successful Rust result are both conclusions. -/
theorem compile_with_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (bytes : Slice U8) (profile : ValidationProfile) (raw : ModuleBinary.Module)
    (limits : runtime.compiler.CompileLimits) (valid : ValidCompilationSource bytes profile raw)
    (eligible : CompileEligible A bytes profile raw limits bound) :
    ∃ executable, runtime.compiler.compile_with ops bytes profile limits = .ok (.Ok executable) := by
  obtain ⟨regions,env,tail,certificate⟩ := StreamCompleteRegions.prepare bytes raw profile valid.encoding valid.signatures
    valid.elaborated valid.typed valid.restrictions
  obtain ⟨bodyBytes,localCount,peak,demand⟩ := eligible.demand regions env tail certificate
  obtain ⟨codeStart,codeEnd,scanned,_,_,_⟩ := certificate.split
  have regionCall : runtime.compiler.code_region bytes = .ok (codeStart,codeEnd) :=
    (compiler_code_region_eq_stream bytes raw valid.encoding).trans scanned
  have available := compiler_source_regions_available bytes regions codeStart codeEnd certificate.split scanned
  have origin : codeStart.val ≤ Itasca.limits.MAX_MODULE_BYTES.val := by
    obtain ⟨ordered,bounded⟩ := Itasca.stream.find_code_region.bounds bytes codeStart codeEnd scanned
    exact (ordered.trans bounded).trans certificate.bounded
  obtain ⟨storage,initialized,_⟩ := WP.spec_imp_exists Itasca.module.Env.new.spec
  obtain ⟨scheduler,run,streamCall,tailEq,tailReady,ready,workers⟩ := compiler_streaming_available ops law bound allocation
    runtime.compiler.CompileSource.Insts.ItascaStreamSource {bytes,code_start := codeStart,code_end := codeEnd} 0#u64 profile
    bytes raw regions env tail certificate available (initialScheduler A limits codeStart) storage bodyBytes localCount peak
    (demand.environment_at codeStart) demand.functions demand.maxima demand.queueReserve rfl rfl rfl rfl origin
  have functionReserve : scheduler.functions.length ≤ bound := by
    change scheduler.functions.val.length ≤ bound
    rw [ready.slots.length]
    have reserve := demand.mappingReserve
    omega
  obtain ⟨⟨reply,budget,pending⟩,collected,budgetEq,functions,status,order⟩ := WP.spec_imp_exists
    (collect_functions_available ops law bound allocation scheduler.budget scheduler.functions functionReserve (by
      intro index inside
      apply ready.slots.filled index
      rw [←ready.slots.length]
      exact inside))
  dsimp only at budgetEq status order
  subst reply
  have functionCount : functions.length = env.func_type_indices.val.length := by
    have counted := congrArg List.length order
    simp only [List.length_map] at counted
    exact counted.symm.trans ready.slots.length
  have paid : CompilationBudgetEffect (initialScheduler A limits 0#usize).budget budget
      (fun counter => env.func_type_indices.val.length*functionDemandRate bodyBytes localCount counter) := by
    rw [budgetEq]
    exact ready.paid
  obtain ⟨⟨reply,executable,finalBudget⟩,lowered,status,_,_,_⟩ := WP.spec_imp_exists
    (initializer_compilation_available ops law bound allocation (uninitializedModule env tail profile functions) budget
      (certificate_initializer_typing certificate functions) (demand.initializers functions functionCount budget paid))
  dsimp only at status
  subst reply
  refine ⟨executable,?_⟩
  unfold runtime.compiler.compile_with
  simp only [if_neg (module_fits bytes limits.max_module_bytes eligible.moduleBytes),regionCall,bind_ok,uncurry_apply_pair,
    Exec.module.Env.new,initialized]
  simp only [initialScheduler] at streamCall
  simp only [Exec.stream.validate_streaming,streamCall,bind_ok,uncurry_apply_pair,tailReady,core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch,collected]
  simp only [uninitializedModule] at lowered
  rw [lowered]
  simp only [bind_ok]
  rfl

end Exec.Code
