import Exec.Store.Linking.LinkErrors
namespace Exec.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 8192
theorem link_staging_errors {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (profile : Itasca.ValidationProfile) (imports : Slice runtime.Extern)
    (store : runtime.store.Store M) (inst : runtime.store.Instance) (index : Usize)
    (status : core.result.Result Unit runtime.ExecError) (allowed : ErrorAllowed (PrecommitError profile) status)
    {out} (run : runtime.store.instantiate.Store.instantiate_inner_loop2 memory store imports status index inst = .ok out) :
    ErrorAllowed (PrecommitError profile) out.2.1 := by
  generalize size : Usize.max - index.val = count
  induction count using Nat.strong_induction_on generalizing store inst index status with
  | h count ih =>
    unfold runtime.store.instantiate.Store.instantiate_inner_loop2 at run
    rw [loop] at run
    simp only [runtime.store.instantiate.Store.instantiate_inner_loop2.body,
      runtime.compiler.ExecutableModule.env, module.Module.env, Itasca.module.Module.impl.env,
      module.Env.types, Itasca.module.Env.impl.types, bind_ok] at run
    split at run
    · cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at run
        subst out
        exact allowed
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at run
        obtain ⟨external, read, rest⟩ := normal_bind_exists _ _ _ run
        obtain ⟨⟨nextStatus, nextStore, nextInst⟩, called, tail⟩ := normal_bind_exists _ _ _ rest
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := normal_bind_exists _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < count := by scalar_tac
        have nextAllowed := (link_import_errors memory profile store inst index external _ called).1
        have nextRun : runtime.store.instantiate.Store.instantiate_inner_loop2 memory nextStore imports nextStatus nextIndex nextInst = .ok out := by
          simpa only [uncurry_apply_pair, bind_ok, runtime.store.instantiate.Store.instantiate_inner_loop2, runtime.store.instantiate.Store.instantiate_inner_loop2.body,
            runtime.compiler.ExecutableModule.env, module.Module.env, Itasca.module.Module.impl.env,
            module.Env.types, Itasca.module.Env.impl.types, core.result.Result.is_ok] using tail
        exact ih _ smaller nextStore nextInst nextIndex nextStatus nextAllowed nextRun rfl
    · simp only [bind_ok, Result.ok.injEq] at run
      subst out
      exact allowed

end Exec.Store
