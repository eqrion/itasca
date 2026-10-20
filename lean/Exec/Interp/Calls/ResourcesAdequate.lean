import Exec.Interp.Calls.CallCauses
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Defined-call resource sufficiency is stated over primitive reserve requests
and independent frame/value bounds, not over the invocation result. -/
theorem CallCause.impossible_of_resources {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {base : Usize} {code : runtime.bytecode.CompiledFunction}
    {error : runtime.ExecError} {bound : Nat}
    (available : Platform.AllocationAvailable allocator bound)
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after))
    (frames : exec.frames.length<store.limits.max_frames.val)
    (values : base.val+code.slot_count.val≤store.limits.max_values.val)
    (frameBound : store.limits.max_frames.val≤bound) (valueBound : store.limits.max_values.val≤bound)
    (cause : CallCause allocator hooks exec store platform base code error) : False := by
  cases error <;> simp only [CallCause] at cause
  all_goals try contradiction
  case Terminated =>
    obtain ⟨after,refused⟩ := cause
    exact continuing _ _ refused
  case Exhausted resource =>
    cases resource <;> simp only [CallCause] at cause
    all_goals try contradiction
    case CallStack => omega
    case Values => omega
    case Allocation =>
      rcases cause with ⟨needed,n,amount,refused⟩ | refused
      · have fits : exec.slots.val.length+n.val≤bound := by change exec.slots.length+n.val≤bound; omega
        rw [available U64 exec.slots n fits] at refused
        simp at refused
      · rw [available runtime.interp.Frame exec.frames 1#usize (by scalar_tac)] at refused
        simp at refused
end Exec.Interp
