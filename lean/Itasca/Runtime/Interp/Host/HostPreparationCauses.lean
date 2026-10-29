import Itasca.Runtime.Interp.Relations.Readback
import Itasca.Runtime.Interp.Relations.Marshal
import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Platform.DivSpec
import Itasca.Runtime.Interp.Host.HostResume
import Itasca.Runtime.Interp.Relations.TypeSlots
import Itasca.Runtime.Interp.Calls.CallRegions

/-!
Host argument/result-buffer preparation and its resource causes. The composition proof tracks requested slot capacity, allocation refusal and the callback boundary while preserving the extracted argument values.
-/

/-! ## Host Arguments -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

@[step] theorem host_arguments_loop (words : alloc.vec.Vec U64)
    (store base : Usize) (results : alloc.vec.Vec runtime.Value)
    (index slot : Usize) (types : alloc.vec.Vec Itasca.types.ValueType) (values : List val)
    (typed : types.val.map sourceType = values.map Compiler.valueType)
    (wellFormed : ∀ value ∈ values, wf_val value)
    (fits : ∀ value ∈ values, ResultIndexFits value)
    (represented : ValuesAt words.val base.val values)
    (bound : index.val ≤ values.length)
    (position : slot.val = base.val + Compiler.offset (values.map Compiler.valueType) index.val)
    (prior : results.val.map sourceValue = values.take index.val) :
    runtime.interp.call_loop0 words results store types index slot ⦃ after =>
      after.val.map sourceValue = values ⦄ := by
  have lengths : types.length = values.length := by
    have h := congrArg List.length typed
    simpa using h
  unfold runtime.interp.call_loop0
  apply loop.spec_decr_nat (fun p => values.length - p.2.1.val)
    (fun p => p.2.1.val ≤ values.length ∧
      p.2.2.val = base.val + Compiler.offset (values.map Compiler.valueType) p.2.1.val ∧
      p.1.val.map sourceValue = values.take p.2.1.val)
  · rintro ⟨current, i, offset⟩ ⟨hi, hoffset, hprior⟩
    dsimp only at hi hoffset hprior
    unfold runtime.interp.call_loop0.body
    dsimp only
    split
    · have hib : i.val < values.length := by scalar_tac
      have hit : i.val < types.val.length := by change i.val < types.length; omega
      let value := values[i.val]
      have hlookup : values[i.val]? = some value := by simp [value, List.getElem?_eq_getElem hib]
      have member : value ∈ values := List.getElem_mem hib
      step as ⟨ty, hty⟩
      have htype : sourceType ty = Compiler.valueType value := by
        have h := congrArg (fun xs => xs[i.val]?) typed
        simpa [List.getElem?_eq_getElem hit, hlookup, ← hty] using h
      have hrep : WordsAt (alloc.vec.Vec.deref words).val offset.val (Compiler.encodeValue value) := by
        have h := represented.lookup hlookup
        simpa [alloc.vec.Vec.deref, hoffset] using h
      step with decode_slot_value (alloc.vec.Vec.deref words) offset ty store value
        (wellFormed value member) htype hrep (fits value member)
        as ⟨decoded, hraw, hdecoded⟩
      have hcurrent : current.length = i.val := by
        have h := congrArg List.length hprior
        simpa [List.length_take, Nat.min_eq_left hi] using h
      step as ⟨after, hafter⟩
      step with width_spec ty as ⟨width, hwidth⟩
      have hnextOffset : base.val + Compiler.offset (values.map Compiler.valueType) (i.val + 1) =
          offset.val + Compiler.width (sourceType ty) := by
        rw [hoffset]
        simp [Compiler.offset, List.take_add_one, hlookup, Compiler.slots_append, Compiler.slots, ← htype, Nat.add_assoc]
      have hcapacity : offset.val + Compiler.width (sourceType ty) ≤ words.length := by
        have hpositive := Compiler.width_positive (sourceType ty)
        have hlen : (Compiler.encodeValue value).length = Compiler.width (sourceType ty) := by
          rw [Compiler.encode_value_length, ← htype]
        have last := hrep ((Compiler.encodeValue value).length - 1) (by omega)
        simp only [alloc.vec.Vec.deref, Slice.from_val] at last
        change offset.val + Compiler.width (sourceType ty) ≤ words.val.length
        omega
      step as ⟨widthSize, hwidthSize⟩
      step as ⟨nextSlot, hnextSlot⟩
      step as ⟨next, hnext⟩
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [hnext, hnextOffset]
        scalar_tac
      · rw [hnext, List.take_add_one, hlookup]
        simp [hafter, hprior, hdecoded, value]
    · have he : i.val = values.length := by scalar_tac
      simpa [WP.spec_ok, he] using hprior
  · exact ⟨bound, position, prior⟩


/-- Host callbacks receive precisely the represented caller argument region. -/
@[step] theorem host_arguments (words : alloc.vec.Vec U64) (store base : Usize)
    (results : alloc.vec.Vec runtime.Value) (types : alloc.vec.Vec Itasca.types.ValueType)
    (values : List val) (empty : results.val = [])
    (typed : types.val.map sourceType = values.map Compiler.valueType)
    (wellFormed : ∀ value ∈ values, wf_val value)
    (fits : ∀ value ∈ values, ResultIndexFits value)
    (represented : ValuesAt words.val base.val values) :
    runtime.interp.call_loop0 words results store types 0#usize base ⦃ after =>
      after.val.map sourceValue = values ⦄ := by
  apply host_arguments_loop words store base results 0#usize base types values typed wellFormed fits represented
  · simp
  · simp [Compiler.offset, Compiler.slots]
  · simp [empty]
end Itasca.Runtime.Interp

end

/-! ## Host Buffers -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

def zeroValue : Itasca.types.ValueType → runtime.Value
  | .I32 => .I32 0#u32
  | .I64 => .I64 0#u64
  | .F32 => .F32 0#u32
  | .F64 => .F64 0#u64
  | .V128 => .V128 0#u128
  | .FuncRef => .FuncRef none
  | .ExternRef => .ExternRef none

@[simp] theorem zero_value_type (ty : Itasca.types.ValueType) : rawType (zeroValue ty) = ty := by
  cases ty <;> rfl

@[simp] theorem zero_value_exact (ty : Itasca.types.ValueType) : runtime.Value.zero ty = .ok (zeroValue ty) := by
  cases ty <;> rfl

/-- Default host results have exactly the signature's arity and raw types. -/
@[step] theorem host_results_defaults_loop (values : alloc.vec.Vec runtime.Value)
    (types : alloc.vec.Vec Itasca.types.ValueType) (index : Usize)
    (bound : index.val ≤ types.length)
    (prior : values.val = (types.val.take index.val).map zeroValue) :
    runtime.interp.call_loop1 values types index ⦃ after => after.val = types.val.map zeroValue ⦄ := by
  unfold runtime.interp.call_loop1
  apply loop.spec_decr_nat (fun p => types.length - p.2.val)
    (fun p => p.2.val ≤ types.length ∧ p.1.val = (types.val.take p.2.val).map zeroValue)
  · rintro ⟨current, i⟩ ⟨hi, currentEq⟩
    dsimp only at hi currentEq ⊢
    unfold runtime.interp.call_loop1.body
    dsimp only
    split
    · have inBounds : i.val < types.length := by scalar_tac
      have currentLength : current.length = i.val := by
        simp only [alloc.vec.Vec.length, currentEq, List.length_map, List.length_take]
        exact Nat.min_eq_left hi
      step as ⟨ty, found⟩
      rw [zero_value_exact]
      simp only [bind_ok]
      step as ⟨after, added⟩
      step as ⟨next, nextEq⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [nextEq, List.take_add_one]
      simp only [List.getElem?_eq_getElem inBounds, added, currentEq, found,
        List.map_append, Option.toList_some, List.map_cons, List.map_nil]
    · have same : i.val = types.length := by scalar_tac
      simpa [WP.spec_ok, same] using currentEq
  · exact ⟨bound, prior⟩

@[step] theorem host_results_defaults (values : alloc.vec.Vec runtime.Value)
    (types : alloc.vec.Vec Itasca.types.ValueType) (empty : values.val = []) :
    runtime.interp.call_loop1 values types 0#usize ⦃ after => after.val = types.val.map zeroValue ⦄ := by
  exact host_results_defaults_loop values types 0#usize (by simp) (by simpa using empty)
end Itasca.Runtime.Interp

end

/-! ## Host Preparation Causes -/

section

namespace Itasca.Runtime.Interp
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
    (typed : signature.params.val.map sourceType = values.map Compiler.valueType)
    (wellFormed : ∀ value ∈ values, wf_val value)
    (fits : ∀ value ∈ values, ResultIndexFits value)
    (represented : ValuesAt exec.slots.val base.val values)
    (cause : Prop)
    (post : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P → Prop)
    (resume : ∀ (ready : runtime.interp.Execution) (nextPlatform : P)
        (args results : alloc.vec.Vec runtime.Value),
      (∃ padding, SlotsEffect exec ready (exec.slots.val ++ padding)) →
      ready.frames = exec.frames →
      base.val + Compiler.slots (signature.results.val.map sourceType) ≤ ready.slots.length →
      args.val.map sourceValue = values → results.val = signature.results.val.map zeroValue →
      DivSpec cause (do
        let (status,p,s,returned) ← hooks.call_host nextPlatform store identity args.slice results.slice
        let (status,finished) ← hostResume memory {ready with host_args := args} s address base
          ⟨returned⟩ status
        Result.ok (status,finished,s,p)) post) :
    DivSpec cause (runtime.interp.call memory hooks floats allocator exec store platform address base) (fun out =>
      (∃ error, out.1 = .Err error ∧ HostPreparationCause allocator hooks exec store platform signature base error ∧ out.2.2.1 = store) ∨ post out) := by
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
            have resultCapacity : base.val + Compiler.slots (signature.results.val.map sourceType) ≤ ready.slots.length := by
              have resultSize : resultWidth.val = Compiler.slots (signature.results.val.map sourceType) := by
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
                have weakened := DivSpec.mono resumed (fun out property =>
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
end Itasca.Runtime.Interp

end
