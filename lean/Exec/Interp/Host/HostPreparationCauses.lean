import Exec.Interp.Host.HostResume
import Exec.Interp.Host.HostArguments
import Exec.Interp.Host.HostBuffers
import Exec.Interp.Relations.TypeSlots
import Exec.Interp.Calls.CallRegions
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Preparation can stop only for allocation, value capacity, or an interrupt.
A continuation theorem separately supplies the callback's source behavior. -/
def HostPreparationError : runtime.ExecError → Prop
  | .Exhausted .Allocation | .Exhausted .Values | .Terminated => True
  | _ => False

/-- Words needed at the caller's argument base for either side of the host signature. -/
def hostSlotDemand (signature : Itasca.types.FuncType) (base : Usize) : Nat :=
  base.val + max (typeSlots signature.results.val) (typeSlots signature.params.val)

/-- Each preparation rejection retains its actual hook decision or a bounded
allocation request. Signature buffers are measured by decoded value counts. -/
def HostPreparationCause {A M P : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (signature : Itasca.types.FuncType)
    (base : Usize) : runtime.ExecError → Prop
  | .Terminated => ∃ next, hooks.interrupt platform = .ok (.Terminate,next)
  | .Exhausted .Values => store.limits.max_values.val < hostSlotDemand signature base
  | .Exhausted .Allocation =>
      (∃ n : Usize, n.val ≤ hostSlotDemand signature base ∧
        allocator.reserve exec.slots n = .ok (false,exec.slots)) ∨
      (∃ n : Usize, n.val ≤ signature.params.val.length ∧
        allocator.reserve exec.host_args n = .ok (false,exec.host_args)) ∨
      (∃ n : Usize, n.val ≤ signature.results.val.length ∧
        allocator.reserve exec.host_results n = .ok (false,exec.host_results))
  | _ => False

theorem HostPreparationCause.error {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {signature : Itasca.types.FuncType}
    {base : Usize} {error : runtime.ExecError}
    (cause : HostPreparationCause allocator hooks exec store platform signature base error) :
    HostPreparationError error := by
  cases error <;> simp_all [HostPreparationCause,HostPreparationError]
  rename_i limit
  cases limit <;> simp_all [HostPreparationCause,HostPreparationError]

private theorem vec_deref_slice {T : Type} (v : alloc.vec.Vec T) : v.deref = v.slice := by
  apply Slice.ext
  simp only [alloc.vec.Vec.deref,Slice.from_val,alloc.vec.Vec.val]

private theorem reserve_result_cause {A T : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (values : alloc.vec.Vec T) (extra : Usize) :
    ∃ answer : Bool, allocator.reserve values extra = .ok (answer,values) ∧
      runtime.reserve allocator values extra = .ok
      ((if answer then .Ok () else .Err (.Exhausted .Allocation)), values) := by
  obtain ⟨answer,reserved⟩ := law.reserve_eq values extra
  refine ⟨answer,reserved,?_⟩
  cases answer <;> simp [runtime.reserve,reserved]

private theorem saturating_sub_le (count used : Usize) :
    (core.num.Usize.saturating_sub count used).val ≤ count.val := by
  simp only [core.num.Usize.saturating_sub,UScalar.saturating_sub,UScalar.val,
    BitVec.toNat_ofNat,Nat.zero_max]
  exact (Nat.mod_le _ _).trans (Nat.sub_le _ _)

/-- Execute the complete extracted host-call preparation, passing the exact
source arguments and zero-initialized result buffer to the callback proof. -/
theorem call_host_composition_causes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (base : Usize)
    (function : runtime.store.FuncInst) (identity : U64) (signature : Itasca.types.FuncType)
    (functionAt : store.funcs.val[address.index.val]? = some function)
    (host : function.code = .Host identity)
    (signatureAt : store.types.val[function.signature.val]? = some signature)
    (values : List val)
    (typed : signature.params.val.map sourceType = values.map Code.valueType)
    (wellFormed : ∀ value ∈ values, wf_val value)
    (fits : ∀ value ∈ values, ResultIndexFits value)
    (represented : ValuesAt exec.slots.val base.val values)
    (post : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P → Prop)
    (resume : ∀ (ready : runtime.interp.Execution) (nextPlatform : P)
        (args results : alloc.vec.Vec runtime.Value),
      (∃ padding, SlotsEffect exec ready (exec.slots.val ++ padding)) →
      ready.frames = exec.frames →
      base.val + Code.slots (signature.results.val.map sourceType) ≤ ready.slots.length →
      args.val.map sourceValue = values → results.val = signature.results.val.map zeroValue →
      (do
        let (status,p,s,returned) ← hooks.call_host nextPlatform store identity args.slice results.slice
        let (status,finished) ← hostResume memory {ready with host_args := args} s address base
          ⟨returned⟩ status
        Result.ok (status,finished,s,p)) ⦃ post ⦄) :
    runtime.interp.call memory hooks floats allocator exec store platform address base ⦃ out =>
      (∃ error, out.1 = .Err error ∧ HostPreparationCause allocator hooks exec store platform signature base error ∧ out.2.2.1 = store) ∨ post out ⦄ := by
  obtain ⟨⟨decision,nextPlatform⟩,decisionEq,_⟩ := WP.spec_imp_exists (interrupts platform)
  unfold runtime.interp.call
  rw [interrupt_eq memory hooks platform nextPlatform decision decisionEq]
  cases decision with
  | Terminate => simp [interruptResult,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,HostPreparationCause,decisionEq]
  | Continue =>
    simp only [interruptResult,bind_ok,core.result.Result.Insts.CoreOpsTry.branch]
    step with vec_index_given store.funcs address.index function functionAt as ⟨found,same⟩
    subst found
    rw [host]
    step with vec_index_given store.types function.signature signature signatureAt as ⟨found,same⟩
    subst found
    step with type_slots_effect signature.results.deref as ⟨result,resultEffect⟩
    cases result with
    | Err error =>
      obtain ⟨rfl,overflow⟩ := resultEffect
      simp only [alloc.vec.Vec.deref,Slice.from_val] at overflow
      have limitMax : store.limits.max_values.val ≤ Usize.max := by scalar_tac
      have excessive : store.limits.max_values.val < hostSlotDemand signature base := by
        unfold hostSlotDemand
        omega
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,HostPreparationCause,excessive]
    | Ok resultWidth =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      step with type_slots_effect signature.params.deref as ⟨params,paramEffect⟩
      cases params with
      | Err error =>
        obtain ⟨rfl,overflow⟩ := paramEffect
        simp only [alloc.vec.Vec.deref,Slice.from_val] at overflow
        have limitMax : store.limits.max_values.val ≤ Usize.max := by scalar_tac
        have excessive : store.limits.max_values.val < hostSlotDemand signature base := by
          unfold hostSlotDemand
          omega
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,HostPreparationCause,excessive]
      | Ok paramWidth =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
        step as ⟨width,widthEq⟩
        simp only [alloc.vec.Vec.deref,Slice.from_val] at resultEffect paramEffect
        have widthSize : width.val = max (typeSlots signature.results.val) (typeSlots signature.params.val) := by
          simp [widthEq,resultEffect,paramEffect]
        have checked := Usize.checked_add_bv_spec base width
        cases sum : Usize.checked_add base width with
        | none =>
          simp only [sum] at checked
          have limitMax : store.limits.max_values.val ≤ Usize.max := by scalar_tac
          have excessive : store.limits.max_values.val < hostSlotDemand signature base := by
            unfold hostSlotDemand
            omega
          simp [sum,lift,HostPreparationCause,excessive]
        | some bound =>
          simp only [sum] at checked ⊢
          simp only [lift,bind_ok]
          step with ensure_effect allocator allocation exec bound store.limits.max_values
            as ⟨status,ready,effect⟩
          cases status with
          | Err error =>
            have boundSize : bound.val = hostSlotDemand signature base := by
              unfold hostSlotDemand
              omega
            cases error <;> simp only [EnsureEffect] at effect
            case Exhausted limit =>
              cases limit <;> simp_all [EnsureEffect,HostPreparationCause,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              all_goals first
              | exact Or.inl effect.1
              | (obtain ⟨_,_,_,n,amount,refused⟩ := effect
                 exact Or.inl (Or.inl ⟨n,by omega,refused⟩))
          | Ok token =>
            cases token
            obtain ⟨limit,slots,fields⟩ := effect
            have length : ready.slots.length = exec.slots.length + (bound.val-exec.slots.length) := by
              change ready.slots.val.length = _
              rw [slots,List.length_append,List.length_replicate]
            have frameEq : ready.frames = exec.frames := by
              have projected := congrArg runtime.interp.Execution.frames fields
              exact projected
            have argsSame : ready.host_args = exec.host_args := by
              have h := congrArg runtime.interp.Execution.host_args fields
              exact h
            have resultsSame : ready.host_results = exec.host_results := by
              have h := congrArg runtime.interp.Execution.host_results fields
              exact h
            have resultCapacity : base.val + Code.slots (signature.results.val.map sourceType) ≤ ready.slots.length := by
              have resultSize : resultWidth.val = Code.slots (signature.results.val.map sourceType) := by
                simpa only [typeSlots,alloc.vec.Vec.deref,Slice.from_val] using resultEffect
              have maximum : resultWidth.val ≤ width.val := by scalar_tac
              scalar_tac
            have argumentSlots : ValuesAt ready.slots.val base.val values := by
              rw [slots]
              exact represented.extend _
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
            let argsAdd := core.num.Usize.saturating_sub signature.params.len ready.host_args.len
            obtain ⟨argsDecision,argsRaw,argsReserve⟩ := reserve_result_cause allocator allocation ready.host_args argsAdd
            rw [argsReserve]
            simp only [bind_ok]
            try dsimp only
            cases argsDecision with
            | false =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,HostPreparationCause]
              exact Or.inl (Or.inr (Or.inl ⟨argsAdd,by simpa [argsAdd] using saturating_sub_le signature.params.len ready.host_args.len,by simpa only [argsSame] using argsRaw⟩))
            | true =>
              simp only [ite_true,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
              let resultsAdd := core.num.Usize.saturating_sub signature.results.len ready.host_results.len
              obtain ⟨resultsDecision,resultsRaw,resultsReserve⟩ := reserve_result_cause allocator allocation ready.host_results resultsAdd
              rw [resultsReserve]
              simp only [bind_ok]
              try dsimp only
              cases resultsDecision with
              | false =>
                simp [core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,HostPreparationCause]
                exact Or.inl (Or.inr (Or.inr ⟨resultsAdd,by simpa [resultsAdd] using saturating_sub_le signature.results.len ready.host_results.len,by simpa only [resultsSame] using resultsRaw⟩))
              | true =>
                simp only [ite_true,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
                step with runtime_clear ready.host_args as ⟨clearedArgs,argsEmpty⟩
                step with runtime_clear ready.host_results as ⟨clearedResults,resultsEmpty⟩
                step with host_arguments ready.slots store.id base clearedArgs signature.params values
                  argsEmpty typed wellFormed fits argumentSlots as ⟨args,argsEq⟩
                step with host_results_defaults clearedResults signature.results resultsEmpty as ⟨results,resultsEq⟩
                have resumed := resume ready nextPlatform args results ⟨_,slots,fields⟩ frameEq resultCapacity argsEq resultsEq
                have weakened := WP.spec_mono resumed (fun out property =>
                  Or.inr property : ∀ out, post out →
                    (∃ error, out.1 = .Err error ∧ HostPreparationCause allocator hooks exec store platform signature base error ∧ out.2.2.1 = store) ∨ post out)
                convert weakened using 1
                simp only [alloc.vec.Vec.deref_mut,vec_deref_slice]
                congr 1
                apply congrArg (fun continuation => Std.bind (hooks.call_host nextPlatform store identity args.slice results.slice) continuation)
                funext answer
                rcases answer with ⟨status,p,s,returned⟩
                simp only [Std.uncurry]
                cases status with
                | Err error => cases error <;> simp [hostResume,bind_ok]
                | Ok token =>
                  cases token
                  try dsimp only
                  simp (config := { zeta := true, zetaDelta := true }) only [hostResume,runtime.interp.call.match_3,runtime.interp.call.match_5,hostResume.match_1,Std.uncurry,alloc.vec.Vec.index_slice_index,Std.bind_assoc,vec_deref_slice]
                  apply congrArg (fun continuation => Std.bind
                    (alloc.vec.Vec.index_usize s.funcs address.index) continuation)
                  funext found
                  apply congrArg (fun continuation => Std.bind
                    (alloc.vec.Vec.index_usize s.types found.signature) continuation)
                  funext signature
                  apply congrArg (fun continuation => Std.bind
                    (runtime.interp.check_values memory s returned signature.results.slice) continuation)
                  funext checked
                  apply congrArg (fun continuation => Std.bind (runtime.interp.check_failed checked) continuation)
                  funext failed
                  cases failed <;> simp [bind_ok,Std.bind_assoc]
end Exec.Interp
