import Exec.Store.Preparation.AllocationCauses
import Exec.Store.Api.Define
namespace Exec.Store
open Aeneas Aeneas.Std

def GlobalAllocationCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) : runtime.ExecError → Prop
  | .Exhausted .Objects => store.limits.max_objects.val ≤ objectCount store
  | .Exhausted .Allocation => allocator.reserve store.globals 1#usize = .ok (false,store.globals)
  | _ => False

theorem define_global_resource_causes {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (ty : Itasca.types.GlobalType) (value : runtime.Value)
    (bound : objectCount store ≤ Usize.max) (typed : ty.valtype = Interp.rawType value)
    (owned : ValueInStore store value) :
    runtime.store.Store.define_global_with memory allocator store ty value
      ⦃ out => ∀ error, out.1 = .Err error → out.2 = store ∧ GlobalAllocationCause allocator store error ⦄ := by
  obtain ⟨words,encoded,_⟩ := WP.spec_imp_exists (Interp.encode_value_spec value store.id owned.1)
  unfold runtime.store.Store.define_global_with
  step with room_spec memory store bound as ⟨room,roomEq⟩
  rw [roomEq]
  split
  · rename_i space
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    rw [check_value_owned memory store value owned.1]
    simp [typed,core.result.Result.Insts.CoreOpsTry.branch,
      core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default]
    obtain ⟨answer,reserved,refusal⟩ := reserve_with_cause allocator law store.globals 1#usize
    rw [reserved]
    cases answer
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,GlobalAllocationCause,refusal]
    · simp [core.result.Result.Insts.CoreOpsTry.branch,encoded]
      cases words with
      | mk lo hi =>
        simp
        have max : store.globals.length < Usize.max := by unfold objectCount at space; scalar_tac
        step
        simp
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,GlobalAllocationCause]
    omega
end Exec.Store
