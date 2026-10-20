import Exec.Theorems.Host.Reentrant.ReentrantPackage
import Exec.Theorems.Instantiation.InstantiateExecutableWorldSource
import Exec.Store.Instantiation.InstantiateNoStartExterns

/-! Checked compilation-backed callback publication. This primitive handles
modules without a start function; nested invocation remains a separate action.
It retains all committed initializer effects and exact precommit rollback. -/
namespace Exec.Theorems.ReentrantCallbacks
open Aeneas Aeneas.Std SpecExt

theorem instantiate_no_start {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform Unit M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _=>True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (package : Package hooks view)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (module : runtime.compiler.ExecutableModule) (imports : Slice runtime.Extern)
    (issued : ∀external∈imports.val,Store.ExternalIssued store external)
    (bytes : Slice U8) (profile : Itasca.ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits=.ok (.Ok module))
    (noStart : module.module.env.start=none) :
    runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator store module imports ()
      ⦃ answer => ∃afterCode,
        ReturnedWorldEffect view (ExecutableInv view) code store afterCode answer.2.1 ∧
        answer.2.1.externs=store.externs ∧
        ∃raw,Itasca.ModuleBinary.ModuleEncodingWith (Itasca.Profile.CodeEncoding profile) raw bytes.val profile ∧
          Module_ok (Itasca.ModuleElaboration.moduleOf raw) ∧
          EventfulInstantiationSourceOutcome view code afterCode store module imports raw () answer.1 answer.2.1 answer.2.2 ⦄ := by
  obtain ⟨raw,encoded,elaborated,matched,typed,rest⟩ :=
    Code.compile_executable_functions allocator allocation bytes profile limits module accepted
  have safe := (instantiate_compiled_executable_world_source memory hooks floats allocator view laws correct allocation
    interrupts store module imports () code held issued bytes profile limits accepted raw encoded package.world_sound
    (fun c s valid identity token args defaults answer actual=>(package.retained c s valid identity token args defaults answer actual).1)
    (fun c s valid identity token args defaults answer actual=>(package.retained c s valid identity token args defaults answer actual).2.1)
    (fun c s valid identity token args defaults answer actual=>(package.retained c s valid identity token args defaults answer actual).2.2)).2
  obtain ⟨answer,actual,shape,accounting,sameToken,externs,result⟩ := WP.spec_imp_exists
    (Store.instantiate_compiled_no_start_externs memory hooks floats allocator view laws allocation store module imports ()
      bytes profile limits accepted held.shape held.segmentAccounting issued noStart)
  rw [actual,WP.dspec_ok] at safe
  rw [actual]
  obtain ⟨afterCode,agrees,fresh,metadata,extension,source⟩ := safe
  exact WP.spec.ret ⟨afterCode,⟨agrees,fresh,metadata,extension⟩,externs,raw,encoded,typed,source⟩
end Exec.Theorems.ReentrantCallbacks
