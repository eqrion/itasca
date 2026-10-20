import Exec.Interp.Invocation.OpenInvoke
import Exec.Interp.Invocation.InvokePrefixCauses
namespace Exec.Interp.OpenCall
open Aeneas Aeneas.Std

/-- Checked invocation setup exposes typed argument slots and empty frames
before entering the resumable call. Every setup rejection has its actual
resource cause and retains the input store. -/
theorem prepare_invoke_checked_effects {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (function : runtime.store.Function)
    (signature : Itasca.types.FuncType) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store=store.id) (hf : store.funcs.val[address.index.val]?=some function)
    (hs : store.types.val[function.signature.val]?=some signature)
    (accepted : runtime.interp.check_values memory store args signature.params.deref=.ok (.Ok ()))
    (owned : ∀value∈args.val,ValueOwnedFits store.id value)
    (post : InvokePhase M P → Prop)
    (early : ∀error,InvocationResourceCause allocator exec store signature results error →
      ∀afterExec,post (.done (.Err error,afterExec,store,platform,results)))
    (handler : ∀prepared p,prepared.store=store.id → prepared.frames.val=[] →
      ValuesAt prepared.slots.val 0 (args.val.map sourceValue) →
      prepared.host_args=exec.host_args → prepared.host_results=exec.host_results →
      prepared.slots.length≤exec.slots.length+typeSlots signature.params.val+typeSlots signature.results.val →
      prepareCall memory hooks floats allocator prepared store p address 0#usize ⦃phase=>post (.waiting phase address results)⦄) :
    prepareInvoke memory hooks floats allocator exec store platform address args results ⦃post⦄ := by
  have tags : signature.params.val = args.val.map rawType := by
    have checked := check_values_accepts_iff memory store args (alloc.vec.Vec.deref signature.params)
    rw [accepted] at checked
    simp only [WP.spec_ok] at checked
    have matched : List.Forall₂ (ArgumentMatches store.id) args.val signature.params.val := by
      simpa only [alloc.vec.Vec.deref, Slice.from_val] using checked.mp trivial
    exact argument_matches_rawtypes matched
  unfold prepareInvoke
  step with func_type_lookup memory store address function signature owner hf hs as ⟨found, same⟩
  subst found
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [accepted]
  simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  step with type_slots_effect (alloc.vec.Vec.deref signature.params) as ⟨params, paramCount⟩
  cases params with
  | Err error =>
    obtain ⟨rfl, overflow⟩ := paramCount
    have cause : ∀afterExec,post (.done (.Err (.Exhausted .Values),afterExec,store,platform,results)) := early _ (by
      simp only [InvocationResourceCause]
      simp only [alloc.vec.Vec.deref, Slice.from_val] at overflow
      have limit : store.limits.max_values.val ≤ Usize.max := by scalar_tac
      omega)
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, cause]
  | Ok params =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with type_slots_effect (alloc.vec.Vec.deref signature.results) as ⟨returns, returnCount⟩
    cases returns with
    | Err error =>
      obtain ⟨rfl, overflow⟩ := returnCount
      have cause : ∀afterExec,post (.done (.Err (.Exhausted .Values),afterExec,store,platform,results)) := early _ (by
        simp only [InvocationResourceCause]
        simp only [alloc.vec.Vec.deref, Slice.from_val] at overflow
        have limit : store.limits.max_values.val ≤ Usize.max := by scalar_tac
        omega)
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, cause]
    | Ok returns =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, lift, bind_ok]
      step with ensure_effect allocator allocation exec (core.cmp.impls.OrdUsize.max params returns) store.limits.max_values
        as ⟨status, grown, growth⟩
      cases status with
      | Err error =>
        have allowed : ∀afterExec,post (.done (.Err error,afterExec,store,platform,results)) := by
          cases error <;> simp only [EnsureEffect] at growth
          all_goals try contradiction
          case Exhausted reason =>
            cases reason <;> simp only [EnsureEffect] at growth
            all_goals try contradiction
            case Values =>
              apply early
              simp only [InvocationResourceCause]
              simp only [alloc.vec.Vec.deref, Slice.from_val] at paramCount returnCount
              scalar_tac
            case Allocation =>
              obtain ⟨within, needed, unchanged, n, amount, reserved⟩ := growth
              apply early
              apply Or.inl
              refine ⟨n, ?_, reserved⟩
              simp only [alloc.vec.Vec.deref, Slice.from_val] at paramCount returnCount
              scalar_tac
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, allowed]
      | Ok unit =>
        cases unit
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with clear_frames grown as ⟨words, frames, hostArgs, hostResults, wordsEq, empty, argsEq, resultsEq⟩
        have capacity : (Code.encodeValues (args.val.map sourceValue)).length ≤ words.length := by
          have length : grown.slots.length = exec.slots.length + ((core.cmp.impls.OrdUsize.max params returns).val - exec.slots.length) := by
            change grown.slots.val.length = _
            rw [growth.2.1, List.length_append, List.length_replicate]
          rw [wordsEq, Code.encodeValues_length]
          simp only [alloc.vec.Vec.deref, typeSlots, Slice.from_val] at paramCount
          have typeEq : (args.val.map sourceValue).map Code.valueType = signature.params.val.map sourceType := by
            rw [tags, List.map_map, List.map_map]
            congr 1
            funext value
            exact sourceValue_type value
          rw [typeEq]
          scalar_tac
        step with marshal_arguments words args signature.params store.id tags owned capacity
          as ⟨encoded, sameLength, represented⟩
        have argsSame : grown.host_args=exec.host_args := by
          have projected := congrArg runtime.interp.Execution.host_args growth.2.2
          exact projected
        have resultsSame : grown.host_results=exec.host_results := by
          have projected := congrArg runtime.interp.Execution.host_results growth.2.2
          exact projected
        have lengthBound : encoded.length≤exec.slots.length+typeSlots signature.params.val+typeSlots signature.results.val := by
          rw [sameLength,wordsEq]
          change grown.slots.val.length≤_
          rw [growth.2.1,List.length_append,List.length_replicate]
          simp only [alloc.vec.Vec.deref,Slice.from_val] at paramCount returnCount
          scalar_tac
        step with handler ⟨store.id,encoded,frames,hostArgs,hostResults⟩ platform rfl empty represented
          (argsEq.trans argsSame) (resultsEq.trans resultsSame) lengthBound as ⟨phase,held⟩
        exact held
end Exec.Interp.OpenCall
