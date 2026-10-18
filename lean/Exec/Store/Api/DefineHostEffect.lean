import Exec.Store.Invariant.TypeStaging
namespace Exec.Store
open Aeneas Aeneas.Std

/-- Host publication only interns a type and appends a host entry. Every old
object remains a prefix and existing module/segment objects are unchanged. -/
structure HostDefinitionEffect {M : Type} (before after : runtime.store.Store M) : Prop where
  retained : StagedPrefix before after
  instances : after.instances = before.instances
  elements : after.elems = before.elems
  datas : after.datas = before.datas
  functions : ∀ fn ∈ after.funcs.val, fn ∈ before.funcs.val ∨ ∃ identity, fn.code = .Host identity

theorem HostDefinitionEffect.intern {M : Type} {before after : runtime.store.Store M}
    {ty status} (effect : InternEffect before ty (status,after)) : HostDefinitionEffect before after := by
  refine ⟨effect.staged, ?_, ?_, ?_, ?_⟩
  all_goals rw [effect.only_types]
  all_goals first | rfl | exact fun fn present => Or.inl present

theorem HostDefinitionEffect.append {M : Type} {before after : runtime.store.Store M}
    (effect : HostDefinitionEffect before after) (signature : Usize) (identity : U64)
    (functions : alloc.vec.Vec runtime.store.Function)
    (appended : functions.val = after.funcs.val ++ [⟨signature,.Host identity⟩]) :
    HostDefinitionEffect before {after with funcs := functions} := by
  have added : StagedPrefix after {after with funcs := functions} := by
    constructor <;> simp [appended]
  refine ⟨effect.retained.trans added,effect.instances,effect.elements,effect.datas,?_⟩
  intro fn present
  change fn ∈ functions.val at present
  rw [appended] at present
  rcases List.mem_append.mp present with old | fresh
  · exact effect.functions fn old
  · have same := List.mem_singleton.mp fresh
    subst fn
    exact Or.inr ⟨identity,rfl⟩

theorem define_host_effect {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (before : runtime.store.Store M) (bound : objectCount before ≤ Usize.max)
    (ty : Itasca.types.FuncType) (identity : U64) :
    runtime.store.Store.define_host_with memory allocator before ty identity
      ⦃ out => HostDefinitionEffect before out.2 ⦄ := by
  unfold runtime.store.Store.define_host_with
  step with intern_type_effect memory allocator law before ty bound as ⟨status, interned, effect⟩
  have retained := HostDefinitionEffect.intern effect
  cases status with
  | Err error =>
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using retained
  | Ok signature =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with room_spec memory interned (effect.object_bound bound) as ⟨room,roomEq⟩
    rw [roomEq]
    by_cases space : objectCount interned < interned.limits.max_objects.val
    · simp only [if_pos space,bind_ok]
      obtain ⟨answer,reserveRun⟩ := reserve_wrapper_eq allocator law interned.funcs 1#usize
      rw [reserveRun]
      cases answer with
      | false =>
        simpa [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using retained
      | true =>
        simp only [↓reduceIte,bind_ok]
        have room : interned.funcs.length < Usize.max := by
          unfold objectCount at space
          scalar_tac
        step as ⟨functions,appended⟩
        exact retained.append signature identity functions appended
    · simpa [if_neg space,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using retained
end Exec.Store
