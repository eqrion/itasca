import Exec.Theorems.Instantiation.InstantiateExecutableSourceOrigin
import Exec.Theorems.Instantiation.InstantiateExecutableTailResources
import Exec.Store.Instantiation.InstantiatePrecommitResources
import Exec.Store.Instantiation.InstantiatePrecommit
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store SpecExt

/-- Factual public instantiation resource evidence. Prepublication refusals
retain the actual rejected computation and its reached preparation phase.
Committed refusals retain generated source allocation and the initialization /
start cause. Invocation signature-buffer demand remains explicit in that cause. -/
def ExecutableInstantiationResourceCause {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (oldCode : CodeInterpretation)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P) (raw : ModuleBinary.Module)
    (error : runtime.ExecError) : Prop :=
  match error with
  | .Exhausted _ | .Terminated =>
    (∃ limit, error = .Exhausted limit ∧ ∃ staged, runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false =
        .ok (.Err error,staged,platform,false) ∧
      PrecommitResourceEvidence memory hooks floats allocator before module imports platform error) ∨
    ∃ ready inst,
      ready.instances.val[before.instances.len.val]? = some inst ∧ inst.module = module ∧
      fun_instantiate (decodeStore view oldCode before) (ModuleElaboration.moduleOf raw) (imports.val.map decodeExternal)
        (sourceInstantiationConfiguration view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) ready inst raw) ∧
      instantiate_tail memory hooks floats allocator ⟨before.id,before.instances.len⟩ ready platform =
        runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false ∧
      ExecutableTailResourceCause memory hooks floats allocator view
        (installCode oldCode before.instances.length (Code.sourceFunctions raw)) ready platform
        ⟨before.id,before.instances.len⟩ inst raw error
  | _ => True

private theorem divergent_return_post {T : Type} {call : Result T} {post extra : T → Prop}
    (safe : call ⦃ result => post result ⦄div)
    (normal : ∀ result, call = .ok result → extra result) :
    call ⦃ result => post result ∧ extra result ⦄div := by
  cases safe with
  | ret property => exact .ret ⟨property,normal _ rfl⟩
  | div => exact .div _

/-- Accepted compilation supplies all initializer and newly installed frame
capacity facts. Every public exhaustion/interrupt result carries its concrete
preparation refusal or source-associated initialization/start cause. -/
theorem instantiate_compiled_executable_resource_causes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (correct : Platform.FloatOpsCorrect floats) (law : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (oldCode : CodeInterpretation) (old : CertifiedExecutableStore view oldCode before)
    (hostFree : CoreHostFree before) (capacities : FunctionCapacities oldCode before)
    (accounted : SegmentAccounting before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (bytes : Slice U8) (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module)) :
    ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧
      Module_ok (ModuleElaboration.moduleOf raw) ∧
      ModuleElaboration.Matches module.module.env module.module.tail raw ∧
      runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
        ⦃ out => ∀ error, out.1 = .Err error →
          ExecutableInstantiationResourceCause memory hooks floats allocator view oldCode before module imports platform raw error ⦄div := by
  obtain ⟨raw,encoded,elaborated,matched,typed,origin⟩ :=
    instantiate_compiled_executable_source_origin memory hooks floats allocator view laws law before module imports platform
      oldCode old hostFree accounted handles bytes profile limits accepted
  refine ⟨raw,encoded,typed,matched,?_⟩
  rcases origin with ⟨error,staged,returned,retained⟩ |
    ⟨ready,inst,found,source,readyCertified,readyCapacities,readyHostFree,readyAccounting,initializers,types,table,allocated,continued⟩
  · obtain ⟨_,_,causes⟩ := instantiate_compiled_precommit_resource_causes memory hooks floats allocator law view laws
      before module imports platform old.shape accounted bytes profile limits accepted handles error staged platform returned
    obtain ⟨out,run,resultEq,storeEq,hostEq⟩ := WP.spec_imp_exists
      (instantiate_rollback memory hooks floats allocator before staged module imports platform platform error retained returned)
    rw [run]
    apply WP.dspec.ret
    intro failed rejected
    have same : error = failed := core.result.Result.Err.inj (resultEq.symm.trans rejected)
    subst failed
    cases error <;> try trivial
    · rename_i limit
      exact Or.inl ⟨limit,rfl,staged,returned,causes⟩
    · have impossible := (instantiate_compiled_precommit_error memory hooks floats allocator law view laws
        before module imports platform old.shape accounted bytes profile limits accepted handles
        .Terminated staged platform returned).1
      simp [PrecommitError] at impossible
  · have acceptedInst : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module) := by
      simpa only [source] using accepted
    have matchedInst : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw := by
      simpa only [source] using matched
    have tail := instantiate_tail_executable_resource_causes memory hooks floats allocator view laws correct law interrupts
      ready platform ⟨before.id,before.instances.len⟩ inst bytes profile limits acceptedInst found
      (installCode oldCode before.instances.length (Code.sourceFunctions raw)) readyCertified readyHostFree
      (readyCapacities capacities) initializers types table raw matchedInst
    have checked := divergent_return_post tail
      (fun out run => instantiate_tail_committed_result memory hooks floats allocator ⟨before.id,before.instances.len⟩ ready platform out run)
    unfold runtime.store.instantiate.Store.instantiate_with
    rw [←continued]
    apply WP.dspec_bind checked
    rintro ⟨result,after,host,committed⟩ ⟨causes,commit⟩
    dsimp only at commit causes ⊢
    subst committed
    cases result with
    | Ok address => simp [runtime.store.instantiation_failed]
    | Err error =>
      simp only [uncurry_apply_pair,runtime.store.instantiation_failed,bind_ok,↓reduceIte,WP.dspec_ok]
      intro failed rejected
      cases rejected
      have cause := causes error rfl
      cases error <;> try trivial
      all_goals exact Or.inr ⟨ready,inst,found,source,allocated,continued,cause⟩
end Exec.Theorems
