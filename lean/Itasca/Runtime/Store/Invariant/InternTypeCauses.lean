import Itasca.Runtime.Store.Preparation.AllocationCauses
import Itasca.Runtime.Store.Invariant.InternTypes
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Concrete thresholds and reached allocator requests for creating one new
canonical signature. Existing signatures return before these checks. -/
def TypeInternResourceCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (ty : Itasca.types.FuncType) : runtime.ExecError → Prop
  | .Exhausted .Objects =>
      Usize.max < ty.params.length + ty.results.length ∨
      store.limits.max_signature_values.val < store.signature_values.val + ty.params.length + ty.results.length ∨
      store.limits.max_objects.val ≤ objectCount store
  | .Exhausted .Allocation =>
      allocator.reserve store.types 1#usize = .ok (false,store.types) ∨ TypeCopyRefusal allocator ty
  | _ => False

theorem intern_type_resource_causes {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (ty : Itasca.types.FuncType)
    (bound : objectCount store ≤ Usize.max) :
    runtime.store.Store.intern_type memory allocator store ty ⦃ out => ∀ error, out.1 = .Err error →
      out.2 = store ∧ ty ∉ store.types.val ∧ TypeInternResourceCause allocator store ty error ⦄ := by
  obtain ⟨scanned,run,index,state,indexBound,priorTypes,found⟩ :=
    WP.spec_imp_exists (intern_scan store ty 0#usize (by scalar_tac) (by simp))
  rw [state] at run
  unfold runtime.store.Store.intern_type
  rw [run]
  simp [scanState]
  split
  · simp
  · rename_i notLess
    have indexEq : index.val = store.types.length := by scalar_tac
    have absent : ty ∉ store.types.val := by simpa [indexEq] using priorTypes
    step as ⟨count,countEq⟩
    cases count with
    | none =>
      simp [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        TypeInternResourceCause,absent]
      exact Or.inl (by scalar_tac)
    | some count =>
      simp [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch]
      step with within_spec store.signature_values count store.limits.max_signature_values as ⟨fits,fitsEq⟩
      rw [fitsEq]
      split
      · rename_i budget
        step with room_spec memory store bound as ⟨room,roomEq⟩
        rw [roomEq]
        by_cases space : objectCount store < store.limits.max_objects.val
        · simp only [if_pos space]
          simp [core.result.Result.Insts.CoreOpsTry.branch]
          obtain ⟨answer,wrapped,called⟩ := reserve_with_cause allocator law store.types 1#usize
          rw [wrapped]
          cases answer
          · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              TypeInternResourceCause,absent,called]
          · simp
            step with copy_type_resource_causes allocator law ty as ⟨copied,effect⟩
            rcases effect with copiedEq | ⟨failed,refusal⟩
            · rw [copiedEq]
              simp [core.result.Result.Insts.CoreOpsTry.branch]
              have room : store.types.length < Usize.max := by unfold objectCount at space; scalar_tac
              step
              step
              simp
            · simp [failed,core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                TypeInternResourceCause,absent,refusal]
        · simp [space,core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            TypeInternResourceCause,absent]
          exact Or.inr (Or.inr (by omega))
      · simp [TypeInternResourceCause,absent]
        exact Or.inr (Or.inl (by scalar_tac))
end Itasca.Runtime.Store
