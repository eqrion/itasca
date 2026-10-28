import Itasca.Runtime.Store.Preparation.AllocationErrors
import Itasca.Runtime.Store.Linking.LinkEffects
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 8192
macro "link_error_step " h:ident : tactic => `(tactic|
  first
  | solve | (simp only [Result.ok.injEq] at $h:ident; cases $h:ident; simp_all [ErrorAllowed, PrecommitError])
  | solve | simp_all only [Result.ok.injEq, Prod.mk.injEq, ErrorAllowed, PrecommitError,
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
theorem link_import_errors {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (profile : Itasca.ValidationProfile) (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (index : Usize) (external : runtime.Extern)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M × runtime.store.ModuleInst)
    (run : runtime.store.instantiate.Store.link_import memory store inst index external = .ok out) :
    ErrorAllowed (PrecommitError profile) out.1 ∧ out.2.1 = store ∧ out.2.2.module = inst.module := by
  unfold runtime.store.instantiate.Store.link_import at run
  repeat' link_error_step run

end Itasca.Runtime.Store
