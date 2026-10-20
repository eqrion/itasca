import Exec.Theorems.Host.Open.Source.Control.Control
import Exec.Theorems.CompilationComplete
import Exec.Theorems.Host.Open.Driver.HostEffects
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Independent refusal permission: there is no valid compilation source
inside the proved eligibility envelope with the required allocations available.
This is not a compiler-return or accepted-trace premise. -/
def CompilationUnavailable {A : Type} (allocator : runtime.platform.Alloc A)
    (bytes : Slice U8) (profile : Itasca.ValidationProfile) (limits : runtime.compiler.CompileLimits) : Prop :=
  ∀bound raw,Code.ValidCompilationSource bytes profile raw → Code.CompileEligible A bytes profile raw limits bound →
    ¬Platform.AllocationAvailable allocator bound

/-- Publication permissions retain independent compilation certificates and
source instantiation outcomes. Refusal and committed instantiation failure are
separate constructors. The supported operation has empty imports and no start. -/
inductive SourcePublicationEffect {M A : Type} (allocator : runtime.platform.Alloc A) (view : M → Slice U8)
    (bytes : Slice U8) (profile : Itasca.ValidationProfile) (limits : runtime.compiler.CompileLimits) :
    store → store → Bool → Prop
  | unavailable {before} (refusal : CompilationUnavailable allocator bytes profile limits) :
      SourcePublicationEffect allocator view bytes profile limits before before false
  | start {before module} (certificate : CompilationCertificate bytes profile module)
      (hasStart : module.module.env.start≠none) :
      SourcePublicationEffect allocator view bytes profile limits before before false
  | instantiated {before after rawBefore rawAfter code afterCode module raw status}
      (certificate : CompilationCertificate bytes profile module)
      (encoded : Itasca.ModuleBinary.ModuleEncodingWith (Itasca.Profile.CodeEncoding profile) raw bytes.val profile)
      (typed : Module_ok (Itasca.ModuleElaboration.moduleOf raw))
      (noStart : module.module.env.start=none)
      (source : EventfulInstantiationSourceOutcome view code afterCode rawBefore module (Slice.new _) raw () status rawAfter ())
      (beforeEq : Store.decodeStore view code rawBefore=before) (afterEq : Store.decodeStore view afterCode rawAfter=after)
      (extension : Extend_store before after) (afterTyped : Store_ok after) :
      SourcePublicationEffect allocator view bytes profile limits before after
        (match status with | .Ok _=>true | .Err _=>false)

def sourcePublication {M A : Type} (allocator : runtime.platform.Alloc A) (view : M → Slice U8) : SourcePublication where
  effect:=SourcePublicationEffect allocator view
  preserves:=by
    intro bytes profile limits before after accepted permission typed
    cases permission with
    | unavailable refusal | start certificate hasStart=>
      exact ⟨Spec.extend_store_refl _ (by cases typed; assumption),typed⟩
    | instantiated certificate encoded sourceTyped noStart source beforeEq afterEq extension afterTyped=>exact ⟨extension,afterTyped⟩

/-- The actual compiler/instantiator implements the publication policy. An
eligible source with available allocations cannot take the refusal branch. -/
theorem publish_source {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (bytes : Slice U8) (profile : Itasca.ValidationProfile) (limits : runtime.compiler.CompileLimits) :
    publish memory floats allocator store bytes profile limits ⦃answer=>∃afterCode,
      ReentrantCallbacks.Effect view code store afterCode answer.2 ∧
      SourcePublicationEffect allocator view bytes profile limits (Store.decodeStore view code store)
        (Store.decodeStore view afterCode answer.2) (match answer.1 with | .Ok _=>true | .Err _=>false)⦄ := by
  obtain ⟨compiled,actual,_⟩ := WP.spec_imp_exists (Code.compile_with_total allocator allocation bytes profile limits)
  unfold publish
  rw [actual,bind_ok]
  cases compiled with
  | Err error=>
    apply WP.spec.ret
    refine ⟨code,.refl held,.unavailable ?_⟩
    intro bound raw valid eligible available
    obtain ⟨module,compiled,certificate⟩ := compile_complete allocator allocation bound available bytes profile raw limits valid eligible
    rw [actual] at compiled
    simp only [Result.ok.injEq] at compiled
    cases compiled
  | Ok module=>
    have certificate := compile_accepted_certificate allocator allocation bytes profile limits module actual
    simp only []
    split
    · rename_i noStart
      obtain ⟨answer,run,afterCode,effect,externs,raw,encoded,typed,source⟩ := WP.spec_imp_exists
        (ReentrantCallbacks.instantiate_no_start_without_callbacks memory (inert memory) floats allocator correct allocation
          (fun _=>WP.spec.ret trivial) view laws code store held module (Slice.new _) (by simp) bytes profile limits actual noStart)
      rw [run,bind_ok]
      have fresh : ReentrantCallbacks.Effect view code store afterCode answer.2.1:=⟨effect,by rw [externs]⟩
      rcases answer with ⟨status,after,token⟩
      cases token
      cases status with
      | Ok address=>exact WP.spec.ret ⟨afterCode,fresh,
          .instantiated certificate encoded typed noStart source rfl rfl effect.extension effect.invariant.source_typed⟩
      | Err error=>exact WP.spec.ret ⟨afterCode,fresh,
          .instantiated certificate encoded typed noStart source rfl rfl effect.extension effect.invariant.source_typed⟩
    · exact WP.spec.ret ⟨code,.refl held,.start certificate (by assumption)⟩
end Exec.Theorems.OpenReentrantControl
