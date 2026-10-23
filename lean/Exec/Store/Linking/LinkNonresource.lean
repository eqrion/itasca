import Exec.Store.Preparation.AllocationErrors
import Exec.Store.Linking.LinkEffects
namespace Exec.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 8192
/-- Link compatibility and ownership checks allocate no execution resources. -/
def LinkFailure (error : runtime.ExecError) : Prop :=
  match error with
  | .Link _ | .WrongStore => True
  | _ => False
macro "link_nonresource_step " h:ident : tactic => `(tactic|
  first
  | solve | (simp only [Result.ok.injEq] at $h:ident; cases $h:ident; simp_all [ErrorAllowed, LinkFailure])
  | solve | simp_all only [Result.ok.injEq, Prod.mk.injEq, ErrorAllowed, LinkFailure,
      runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.option.Option.ok_or, bind_ok, bind_tc_ok]
  | (fail_if_no_progress simp only [runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.option.Option.ok_or, bind_ok, bind_tc_ok, uncurry_apply_pair] at $h:ident)
  | split at $h:ident
  | (obtain ⟨value, called, rest⟩ := normal_bind_exists _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue, secondValue⟩
        repeat' (guard_hyp secondValue : Prod _ _; rcases secondValue with ⟨firstValue, secondValue⟩))
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | split at $h:ident)

/-- Linking itself can reject only compatibility or handle ownership. Partial
indexing is excluded by normal return here, and by issued-handle invariants in
the surrounding total staging theorem. -/
theorem link_import_nonresource {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (index : Usize) (external : runtime.Extern)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M × runtime.store.ModuleInst)
    (run : runtime.store.instantiate.Store.link_import memory store inst index external = .ok out) :
    ErrorAllowed (LinkFailure) out.1 ∧ out.2.1 = store ∧ out.2.2.module = inst.module := by
  unfold runtime.store.instantiate.Store.link_import at run
  repeat' link_nonresource_step run

theorem link_staging_nonresource {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (imports : Slice runtime.Extern)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (status : core.result.Result Unit runtime.ExecError) (allowed : ErrorAllowed LinkFailure status)
    {out} (run : runtime.store.instantiate.Store.instantiate_inner_loop2 memory store imports status index inst = .ok out) :
    ErrorAllowed LinkFailure out.2.1 := by
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
        have nextAllowed := (link_import_nonresource memory store inst index external _ called).1
        have nextRun : runtime.store.instantiate.Store.instantiate_inner_loop2 memory nextStore imports nextStatus nextIndex nextInst = .ok out := by
          simpa only [uncurry_apply_pair, bind_ok, runtime.store.instantiate.Store.instantiate_inner_loop2, runtime.store.instantiate.Store.instantiate_inner_loop2.body,
            runtime.compiler.ExecutableModule.env, module.Module.env, Itasca.module.Module.impl.env,
            module.Env.types, Itasca.module.Env.impl.types, core.result.Result.is_ok] using tail
        exact ih _ smaller nextStore nextInst nextIndex nextStatus nextAllowed nextRun rfl
    · simp only [bind_ok, Result.ok.injEq] at run
      subst out
      exact allowed

end Exec.Store
