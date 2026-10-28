import Itasca.Runtime.Interp.Relations.Ensure
import Itasca.Runtime.Interp.Relations.InitLocals
import Itasca.Runtime.Interp.Relations.Fetch
import Itasca.Runtime.Interp.Numeric.Integer.Interrupt

/-! Defined-function entry checks resources, initializes local words, and pushes
a frame. These operations return normally under the explicit allocation and
interrupt laws, and cannot mutate the store. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Exact successful entry state; all invocation scratch fields are preserved. -/
def CallEntryEffect (before after : runtime.interp.Execution)
    (instanceIndex functionIndex base : Usize) (code : runtime.bytecode.CompiledFunction) : Prop :=
  after.frames.val = before.frames.val ++
    [{ «instance» := instanceIndex, function := functionIndex, pc := 0#u32, base := base }] ∧
  after.slots.val = zeroWords
    (before.slots.val ++ List.replicate
      (base.val + code.slot_count.val - before.slots.length) 0#u64)
    (base.val + code.param_slots.val) (code.local_slots.val - code.param_slots.val) ∧
  { after with slots := before.slots, frames := before.frames } = before

theorem call_wasm_effect {M P F A : Type}
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
      ⦃ out => out.2.2.1 = store ∧
        (out.1 = .Ok () → CallEntryEffect exec out.2.1 instanceIndex functionIndex base code) ⦄ := by
  obtain ⟨⟨decision, afterPlatform⟩, hdecision, _⟩ := WP.spec_imp_exists (interrupts platform)
  unfold runtime.interp.call
  rw [interrupt_eq memory hooks platform afterPlatform decision hdecision]
  cases decision with
  | Terminate =>
    simp [interruptResult, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Continue =>
    simp only [interruptResult, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    step with vec_index_given store.funcs address.index function hf as ⟨found, hfound⟩
    subst found
    rw [hw]
    dsimp only
    split
    · simp
    · rename_i room
      step with vec_index_given store.instances instanceIndex inst hi as ⟨found, hfound⟩
      subst found
      step with vec_index_given inst.module.functions functionIndex code hc as ⟨found, hfound⟩
      subst found
      simp only [lift, bind_ok]
      have hchecked := Usize.checked_add_bv_spec base (UScalar.cast .Usize code.slot_count)
      cases hend : Usize.checked_add base (UScalar.cast .Usize code.slot_count) with
      | none => simp [hend]
      | some bound =>
        simp only [hend] at hchecked ⊢
        step with ensure_effect allocator allocation exec bound store.limits.max_values
          as ⟨result, afterEnsure, heffect⟩
        cases result with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
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
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | true =>
            simp [core.result.Result.Insts.CoreOpsTry.branch]
            have hcapacity : afterInit.frames.length < Usize.max := by
              rw [hframes']
              scalar_tac
            step as ⟨frames, happend⟩
            intro _
            refine ⟨?_, ?_, ?_⟩
            · simpa [hframes'] using happend
            · simp only [hwords, hslots, hstart, U32.cast_Usize_val_eq, hbound,
                Nat.add_sub_add_left]
            · have he : { afterInit with slots := exec.slots } = exec := by
                calc
                  _ = { afterEnsure with slots := exec.slots } :=
                    congrArg (fun e : runtime.interp.Execution => { e with slots := exec.slots }) hfields
                  _ = exec := hrest
              have h := congrArg (fun e : runtime.interp.Execution => { e with frames := exec.frames }) he
              exact h

end Itasca.Runtime.Interp
