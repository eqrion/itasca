import Itasca.Runtime.Interp.Recording
import Itasca.Runtime.Interp.Relations.SlotsAndDefaults
import Itasca.Runtime.Interp.Numeric.Integer.SignedOperationsAndCounts

open Itasca.Representation

/-! ## Call -/

section

/-! Defined-function entry checks resources, initializes local words, and pushes
a frame. These operations return normally under the explicit allocation and
interrupt laws, and cannot mutate the store. -/
namespace Itasca.Interp
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

end Itasca.Interp

end

/-! ## DirectCall -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std

/-- Resolving a direct call uses the caller's instance map and the emitted
callee-base offset. The callee's own instance is resolved by `call`. -/
theorem execute_call_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (callerIndex base : Usize) (func callee : U32)
    (caller : runtime.store.ModuleInst) (address : runtime.FuncAddr) (calleeBase : Usize)
    (hi : store.instances.val[callerIndex.val]? = some caller)
    (ha : caller.funcs.val[func.val]? = some address)
    (hb : calleeBase.val = base.val + callee.val)
    (cause : Prop) (post : core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
      runtime.store.Store M × P → Prop)
    (called : Computation.DivSpec cause (runtime.interp.call memory hooks floats allocator exec store platform
      address calleeBase) post) :
    Computation.DivSpec cause (runtime.interp.execute_call memory hooks floats allocator exec store platform
      callerIndex base func callee) post := by
  unfold runtime.interp.execute_call
  step with vec_index_given store.instances callerIndex caller hi as ⟨found, hfound⟩
  subst found
  simp only [lift, bind_ok]
  step with vec_index_given caller.funcs (UScalar.cast .Usize func) address
    (by simpa only [U32.cast_Usize_val_eq] using ha) as ⟨found, hfound⟩
  subst found
  step as ⟨actualBase, hbase⟩
  have heq : actualBase = calleeBase := by scalar_tac
  subst actualBase
  exact called

/-- Full instruction fetch advances the caller PC before entering a direct
callee, so successful return resumes after the CALL instruction. -/
theorem step_direct_call {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (frame : runtime.interp.Frame)
    (caller : runtime.store.ModuleInst) (callerCode : runtime.bytecode.CompiledFunction)
    (func callee : U32) (address : runtime.FuncAddr) (calleeBase : Usize)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some frame)
    (hi : store.instances.val[frame.instance.val]? = some caller)
    (hc : caller.module.functions.val[frame.function.val]? = some callerCode)
    (hop : callerCode.code.val[frame.pc.val]? = some (.Call func callee))
    (pcBound : frame.pc.val < U32.max)
    (ha : caller.funcs.val[func.val]? = some address)
    (hb : calleeBase.val = frame.base.val + callee.val)
    (cause : Prop) (post : core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
      runtime.store.Store M × P → Prop)
    (called : ∀ next : U32, next.val = frame.pc.val + 1 →
      Computation.DivSpec cause (runtime.interp.call memory hooks floats allocator
        { exec with frames := exec.frames.set index { frame with pc := next } }
        store platform address calleeBase) post) :
    Computation.DivSpec cause (runtime.interp.step memory hooks floats allocator exec store platform) post := by
  apply step_fetch_div memory hooks floats allocator exec store platform index frame
    caller callerCode (.Call func callee) last hf hi hc hop pcBound cause post
  intro next hnext
  exact execute_call_effect memory hooks floats allocator _ store platform
    frame.instance frame.base func callee caller address calleeBase hi ha hb cause post (called next hnext)

end Itasca.Interp

end

/-! Callback observation preserves the extracted computation under erasure. -/

namespace Itasca.Interp
open Aeneas Aeneas.Std Itasca.Platform

/-- The extracted call has no access to the observer's log. This equation also
covers callback failure and divergence; no execution invariant is needed. -/
theorem observing_call_execution_erase {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (base : Usize) (prior : List (HostObservation M)) :
    (do let (result, nextExec, after, next, _) ←
          runtime.interp.call memory (observing hooks) floats allocator exec store (platform, prior) address base
        Result.ok (result, nextExec, after, next)) =
      runtime.interp.call memory hooks floats allocator exec store platform address base := by
  unfold runtime.interp.call
  simp only [Itasca.Platform.observing, Std.bind_assoc, bind_ok, Std.uncurry]
  repeat' first
    | rfl
    | (apply bind_project _ _ _ _ _ (observing_interrupt_execution_erase ..)
       rintro ⟨decision, next, trace⟩
       simp only [Std.uncurry])
    | (apply congrArg (Std.bind _); funext answer)
    | (split <;> simp_all only [Std.bind_assoc, bind_ok, Std.uncurry])
  all_goals cases answer.code <;> dsimp only
  all_goals try simp only [Std.bind_assoc]
  all_goals repeat' first
    | rfl
    | (apply congrArg (Std.bind _); funext answer)
    | (split <;> simp_all only [Std.bind_assoc, bind_ok, Std.uncurry])

theorem observing_execute_call_erase {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (inst base : Usize) (func callee : U32) (prior : List (HostObservation M)) :
    (do let (result, nextExec, after, next, _) ←
          runtime.interp.execute_call memory (observing hooks) floats allocator exec store (platform, prior) inst base func callee
        Result.ok (result, nextExec, after, next)) =
      runtime.interp.execute_call memory hooks floats allocator exec store platform inst base func callee := by
  unfold runtime.interp.execute_call
  simp only [Std.bind_assoc]
  repeat' first
    | rfl
    | exact observing_call_execution_erase ..
    | (apply congrArg (Std.bind _); funext answer)



/-- Entering a Wasm function cannot append a callback observation. Subsequent
instructions in that function are handled by the dispatch proof. -/
theorem observing_call_wasm_lift {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (base : Usize) (prior : List (HostObservation M))
    (wasm : ∃ function instanceIndex functionIndex,
      store.funcs.val[address.index.val]? = some function ∧
      function.code = .Wasm instanceIndex functionIndex) :
    runtime.interp.call memory (observing hooks) floats allocator exec store (platform, prior) address base =
      (do let (result, nextExec, after, next) ←
            runtime.interp.call memory hooks floats allocator exec store platform address base
          Result.ok (result, nextExec, after, next, prior)) := by
  obtain ⟨function, instanceIndex, functionIndex, found, code⟩ := wasm
  unfold runtime.interp.call
  rw [observing_interrupt_execution_lift]
  simp only [Std.bind_assoc, bind_ok, Std.uncurry]
  apply congrArg (Std.bind _)
  funext pair
  rcases pair with ⟨status, next⟩
  cases status <;> simp only [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    bind_ok, vec_index_eq _ _ _ found, code]
  all_goals try simp only [Std.bind_assoc, bind_ok, Std.uncurry]
  all_goals repeat' first
    | rfl
    | (apply congrArg (Std.bind _); funext answer)
    | (split <;> simp_all only [Std.bind_assoc, bind_ok, Std.uncurry])


private theorem vec_index_none {T : Type} (values : alloc.vec.Vec T) (index : Usize)
    (missing : values.val[index.val]? = none) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice T) values index =
      .fail .arrayOutOfBounds := by
  rw [alloc.vec.Vec.index_slice_index]
  change (match values.val[index.val]? with | none => Result.fail .arrayOutOfBounds | some x => .ok x) = _
  rw [missing]

theorem observing_call_nonhost_lift {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (base : Usize) (prior : List (HostObservation M))
    (nonhost : ∀ function identity, store.funcs.val[address.index.val]? = some function →
      function.code ≠ .Host identity) :
    runtime.interp.call memory (observing hooks) floats allocator exec store (platform, prior) address base =
      (do let (result, nextExec, after, next) ←
            runtime.interp.call memory hooks floats allocator exec store platform address base
          Result.ok (result, nextExec, after, next, prior)) := by
  cases found : store.funcs.val[address.index.val]? with
  | some function =>
    cases code : function.code with
    | Host identity => exact False.elim (nonhost function identity found code)
    | Wasm inst index =>
      exact observing_call_wasm_lift memory hooks floats allocator exec store platform
        address base prior ⟨function,inst,index,found,code⟩
  | none =>
    unfold runtime.interp.call
    rw [observing_interrupt_execution_lift]
    simp only [Std.bind_assoc, bind_ok, Std.uncurry]
    apply congrArg (Std.bind _)
    funext pair
    rcases pair with ⟨status, next⟩
    cases status <;> simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      bind_ok, vec_index_none _ _ found, bind_fail]
    all_goals simp only [Std.bind_assoc, bind_ok, Std.uncurry]


theorem observing_execute_call_nonhost_lift {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (inst base : Usize) (func callee : U32) (prior : List (HostObservation M))
    (nonhost : ∀ caller address function identity,
      store.instances.val[inst.val]? = some caller → caller.funcs.val[func.val]? = some address →
      store.funcs.val[address.index.val]? = some function → function.code ≠ .Host identity) :
    runtime.interp.execute_call memory (observing hooks) floats allocator exec store (platform, prior)
      inst base func callee =
      (do let (result, nextExec, after, next) ←
            runtime.interp.execute_call memory hooks floats allocator exec store platform inst base func callee
          Result.ok (result, nextExec, after, next, prior)) := by
  unfold runtime.interp.execute_call
  cases instanceAt : store.instances.val[inst.val]? with
  | none => simp only [vec_index_none _ _ instanceAt, bind_fail]
  | some caller =>
    simp only [vec_index_eq _ _ _ instanceAt, bind_ok, lift]
    cases addressAt : caller.funcs.val[func.val]? with
    | none =>
      have missing : caller.funcs.val[(UScalar.cast .Usize func).val]? = none := by
        simpa only [U32.cast_Usize_val_eq] using addressAt
      simp only [vec_index_none _ _ missing, bind_fail]
    | some address =>
      have found : caller.funcs.val[(UScalar.cast .Usize func).val]? = some address := by
        simpa only [U32.cast_Usize_val_eq] using addressAt
      simp only [vec_index_eq _ _ _ found, bind_ok, Std.bind_assoc]
      apply congrArg (Std.bind _)
      funext nextBase
      exact observing_call_nonhost_lift memory hooks floats allocator exec store platform address nextBase prior
        (fun function identity atFunction => nonhost caller address function identity instanceAt addressAt atFunction)

end Itasca.Interp

/- Callback correspondence for normally returned call instructions. -/
namespace Itasca.Interp
open Aeneas Aeneas.Std Itasca.Platform

theorem observing_execute_call_returned {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (calls : Observation.Call memory hooks floats allocator)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (raw : runtime.interp.Frame) (operands : U32 × U32) (prior : List (HostObservation M))
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M ×
      (P × List (HostObservation M)))
    (run : runtime.interp.execute_call memory (observing hooks) floats allocator exec store (platform,prior)
      raw.instance raw.base operands.1 operands.2 = .ok out) :
    ∀ caller compiled, store.instances.val[raw.instance.val]? = some caller →
      ObservationExtension prior out.2.2.2.2
        (match hostInstructionAddress exec store raw caller compiled (.Call operands.1 operands.2) with
         | some address => hostCallEvents address out | none => []) := by
  intro caller compiled callerAt
  unfold runtime.interp.execute_call at run
  simp only [vec_index_eq _ _ _ callerAt,lift,bind_ok] at run
  obtain ⟨address,addressRead,run⟩ := Computation.bind_ok_inv _ _ _ run
  have addressAt := vec_index_observed _ _ _ addressRead
  simp only [U32.cast_Usize_val_eq] at addressAt
  obtain ⟨base,_,run⟩ := Computation.bind_ok_inv _ _ _ run
  have observed := calls exec store platform address base prior out run
  cases found : store.funcs.val[address.index.val]? with
  | none => simpa only [hostInstructionAddress,Bind.bind,Option.bind,addressAt,found,callHostEvents] using observed
  | some function =>
    cases code : function.code <;>
      simpa only [hostInstructionAddress,Bind.bind,Option.bind,addressAt,found,code,callHostEvents] using observed
end Itasca.Interp
