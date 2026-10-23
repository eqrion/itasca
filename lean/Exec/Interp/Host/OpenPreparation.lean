import Exec.Interp.Host.OpenCall
import Exec.Interp.Host.HostArgumentsOwned
namespace Exec.Interp.OpenCall
open Aeneas Aeneas.Std

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

def PreparedHostOutcome {M P A : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (address : runtime.FuncAddr) (base : Usize)
    (identity : U64) (signature : Itasca.types.FuncType) (values : List val) (phase : CallPhase M P) : Prop :=
  (∃out,phase=.done out ∧ ∃error,out.1=.Err error ∧
    HostPreparationCause allocator hooks exec store platform signature base error ∧ out.2.2.1=store) ∨
  ∃ready nextPlatform args defaults,
    phase=.pending {ready with host_args:=args} store nextPlatform address base identity args defaults ∧
    (∃padding,SlotsEffect exec ready (exec.slots.val++padding)) ∧ ready.frames=exec.frames ∧
    base.val+Code.slots (signature.results.val.map sourceType)≤ready.slots.length ∧
    args.val.map sourceValue=values ∧ defaults.val=signature.results.val.map zeroValue

def PreparedHostEffects {M P A : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (address : runtime.FuncAddr) (base : Usize)
    (identity : U64) (signature : Itasca.types.FuncType) (values : List val) (phase : CallPhase M P) : Prop :=
  (∃out,phase=.done out ∧ ∃error,out.1=.Err error ∧
    HostPreparationCause allocator hooks exec store platform signature base error ∧ out.2.2.1=store) ∨
  ∃ready nextPlatform args defaults,
    phase=.pending {ready with host_args:=args} store nextPlatform address base identity args defaults ∧
    (∃padding,SlotsEffect exec ready (exec.slots.val++padding)) ∧ ready.frames=exec.frames ∧
    base.val+Code.slots (signature.results.val.map sourceType)≤ready.slots.length ∧
    args.val.map sourceValue=values ∧ defaults.val=signature.results.val.map zeroValue ∧
    ready.slots.length≤exec.slots.length+hostSlotDemand signature base ∧
    (∀value∈args.val,OwnedBy store.id value)

theorem prepare_host_call_effects {M P F A : Type}
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
 :
    prepareCall memory hooks floats allocator exec store platform address base
      ⦃ phase=>PreparedHostEffects allocator hooks exec store platform address base identity signature values phase ⦄ := by
  obtain ⟨⟨decision,nextPlatform⟩,decisionEq,_⟩ := WP.spec_imp_exists (interrupts platform)
  unfold prepareCall
  rw [interrupt_eq memory hooks platform nextPlatform decision decisionEq]
  cases decision with
  | Terminate => simp [interruptResult,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,PreparedHostEffects,HostPreparationCause,decisionEq]
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
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,PreparedHostEffects,HostPreparationCause,excessive]
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
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,PreparedHostEffects,HostPreparationCause,excessive]
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
          simp [sum,lift,PreparedHostEffects,HostPreparationCause,excessive]
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
              cases limit <;> simp_all [EnsureEffect,PreparedHostEffects,HostPreparationCause,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              all_goals first
              | exact Or.inl effect.1
              | (obtain ⟨_,_,_,n,amount,refused⟩ := effect
                 exact Or.inl ⟨n,by omega,refused⟩)
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
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,PreparedHostEffects,HostPreparationCause]
              exact Or.inr (Or.inl ⟨argsAdd,by simpa [argsAdd] using saturating_sub_le signature.params.len ready.host_args.len,by simpa only [argsSame] using argsRaw⟩)
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
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,PreparedHostEffects,HostPreparationCause]
                exact Or.inr (Or.inr ⟨resultsAdd,by simpa [resultsAdd] using saturating_sub_le signature.results.len ready.host_results.len,by simpa only [resultsSame] using resultsRaw⟩)
              | true =>
                simp only [ite_true,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
                step with runtime_clear ready.host_args as ⟨clearedArgs,argsEmpty⟩
                step with runtime_clear ready.host_results as ⟨clearedResults,resultsEmpty⟩
                step with host_arguments_owned ready.slots store.id base clearedArgs signature.params values
                  argsEmpty typed wellFormed fits argumentSlots as ⟨args,argsEq,argsOwned⟩
                step with host_results_defaults clearedResults signature.results resultsEmpty as ⟨results,resultsEq⟩
                have demandSize : bound.val=hostSlotDemand signature base := by unfold hostSlotDemand; omega
                have lengthBound : ready.slots.length≤exec.slots.length+hostSlotDemand signature base := by rw [length,demandSize]; omega
                exact WP.spec.ret (Or.inr ⟨ready,nextPlatform,args,results,rfl,⟨_,slots,fields⟩,frameEq,resultCapacity,argsEq,resultsEq,lengthBound,argsOwned⟩)

theorem prepare_host_call {M P F A : Type}
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
 :
    prepareCall memory hooks floats allocator exec store platform address base
      ⦃ phase=>PreparedHostOutcome allocator hooks exec store platform address base identity signature values phase ⦄ := by
  apply WP.spec_mono (prepare_host_call_effects memory hooks floats allocator allocation interrupts exec store platform address base
    function identity signature functionAt host signatureAt values typed wellFormed fits represented)
  intro phase post
  rcases post with early|pending
  · exact Or.inl early
  · obtain ⟨ready,nextPlatform,args,defaults,same,padding,frames,capacity,argsEq,defaultsEq,lengthBound,argsOwned⟩ := pending
    exact Or.inr ⟨ready,nextPlatform,args,defaults,same,padding,frames,capacity,argsEq,defaultsEq⟩
end Exec.Interp.OpenCall
