import Exec.Interp.Calls.Call
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Each defined-call rejection has a concrete resource or interrupt cause.
Allocation witnesses name exactly the slot/frame vectors used at entry. -/
def CallCause {A M P : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (before : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (base : Usize)
    (code : runtime.bytecode.CompiledFunction) : runtime.ExecError → Prop
  | .Terminated => ∃ after, hooks.interrupt platform = .ok (.Terminate, after)
  | .Exhausted .CallStack => store.limits.max_frames.val ≤ before.frames.length
  | .Exhausted .Values => store.limits.max_values.val < base.val + code.slot_count.val
  | .Exhausted .Allocation =>
      (before.slots.length < base.val + code.slot_count.val ∧
        ∃ n : Usize, n.val = base.val + code.slot_count.val - before.slots.length ∧
          allocator.reserve before.slots n = .ok (false, before.slots)) ∨
      allocator.reserve before.frames 1#usize = .ok (false, before.frames)
  | _ => False

theorem call_wasm_causes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (base : Usize)
    (function : runtime.store.FuncInst) (instanceIndex functionIndex : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (hi : store.instances.val[instanceIndex.val]? = some inst)
    (hc : inst.module.functions.val[functionIndex.val]? = some code)
    (params : code.param_slots.val ≤ code.local_slots.val)
    (locals : code.local_slots.val ≤ code.slot_count.val) :
    runtime.interp.call memory hooks floats allocator exec store platform address base
      ⦃ out => ∀ error, out.1 = .Err error →
        CallCause allocator hooks exec store platform base code error ⦄ := by
  obtain ⟨⟨decision, afterPlatform⟩, hdecision, _⟩ := WP.spec_imp_exists (interrupts platform)
  unfold runtime.interp.call
  rw [interrupt_eq memory hooks platform afterPlatform decision hdecision]
  cases decision with
  | Terminate =>
    simp [interruptResult, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CallCause]
    exact ⟨afterPlatform, hdecision⟩
  | Continue =>
    simp only [interruptResult, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    step with vec_index_given store.funcs address.index function hf as ⟨found, hfound⟩
    subst found
    rw [hw]
    dsimp only
    split
    · simp [CallCause]
      scalar_tac
    · rename_i room
      step with vec_index_given store.instances instanceIndex inst hi as ⟨found, hfound⟩
      subst found
      step with vec_index_given inst.module.functions functionIndex code hc as ⟨found, hfound⟩
      subst found
      simp only [lift, bind_ok]
      have hchecked := Usize.checked_add_bv_spec base (UScalar.cast .Usize code.slot_count)
      cases hend : Usize.checked_add base (UScalar.cast .Usize code.slot_count) with
      | none =>
        simp only [hend] at hchecked
        simp [CallCause]
        scalar_tac
      | some bound =>
        simp only [hend] at hchecked ⊢
        step with ensure_effect allocator allocation exec bound store.limits.max_values
          as ⟨result, afterEnsure, heffect⟩
        cases result with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          have hbound : bound.val = base.val + code.slot_count.val := by
            simpa only [U32.cast_Usize_val_eq] using hchecked.2.1
          cases error <;> simp only [EnsureEffect] at heffect
          all_goals try contradiction
          case Exhausted resource =>
            cases resource <;> simp only [EnsureEffect] at heffect
            all_goals try contradiction
            case Values =>
              simp only [CallCause]
              omega
            case Allocation =>
              apply Or.inl
              obtain ⟨hlimit, hneeded, hstate, n, hn, hr⟩ := heffect
              exact ⟨by omega, n, by omega, hr⟩
        | Ok unit =>
          cases unit
          obtain ⟨hlimit, hslots, hrest⟩ := heffect
          have hlength : afterEnsure.slots.length =
              exec.slots.length + (bound.val - exec.slots.length) := by
            change afterEnsure.slots.val.length = _
            rw [hslots, List.length_append, List.length_replicate]
          have hframes : afterEnsure.frames = exec.frames := by
            have h := congrArg runtime.interp.Execution.frames hrest
            exact h
          have hbound : bound.val = base.val + code.slot_count.val := by
            simpa only [U32.cast_Usize_val_eq] using hchecked.2.1
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift]
          step as ⟨start, hstart⟩
          step with init_locals_effect afterEnsure base code.local_slots start
            (by omega) (by scalar_tac) as ⟨afterInit, hinit⟩
          obtain ⟨hwords, hfields⟩ := hinit
          have hframes' : afterInit.frames = exec.frames := by
            have h := congrArg runtime.interp.Execution.frames hfields
            exact h.trans hframes
          obtain ⟨answer, hreserve⟩ := allocation.reserve_eq afterInit.frames 1#usize
          unfold runtime.reserve
          rw [hreserve, bind_ok]
          cases answer with
          | false =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CallCause]
            exact Or.inr (by simpa only [hframes'] using hreserve)
          | true =>
            simp [core.result.Result.Insts.CoreOpsTry.branch]
            have hcapacity : afterInit.frames.length < Usize.max := by
              rw [hframes']
              scalar_tac
            step
            simp


end Itasca.Runtime.Interp
