import Exec.Theorems.Host.HostCallSource
import Exec.Interp.Relations.FrameStorePrefix
import Exec.Theorems.Host.Chosen.HostResumeChosen
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

def ChosenHostCallSourceOutcome (choices : Spec.SourceChoices) (occurrence : Nat) {M P : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (before : runtime.store.Store M) (ambient : frame) (address : runtime.FuncAddr)
    (args : List val) (base : Usize) (exec : runtime.interp.Execution)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : Prop :=
  out.2.1.host_args.val.map sourceValue = args ∧ out.2.1.frames = exec.frames ∧ out.2.1.store = exec.store ∧
  exec.slots.length ≤ out.2.1.slots.length ∧
  ((out.1 = .Ok () ∧
    ValuesAt out.2.1.slots.val base.val (out.2.1.host_results.val.map sourceValue) ∧
    Spec.ChoiceStep choices occurrence ⟨⟨Store.decodeStore view code before,ambient⟩,vals args ++ [.CALL_ADDR address.index.val]⟩
      [.call address.index.val args (some (out.2.1.host_results.val.map sourceValue))]
      ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,vals (out.2.1.host_results.val.map sourceValue)⟩ ∧
    (∀ j, j < exec.slots.length →
      j < base.val ∨ base.val + Code.slots (out.2.1.host_results.val.map (Code.valueType ∘ sourceValue)) ≤ j →
      out.2.1.slots.val[j]? = exec.slots.val[j]?)) ∨
   ((out.1 = .Err (.Trap .Host) ∨ out.1 = .Err (.Exhausted .CallStack)) ∧
    Spec.ChoiceStep choices occurrence ⟨⟨Store.decodeStore view code before,ambient⟩,vals args ++ [.CALL_ADDR address.index.val]⟩
      [.call address.index.val args none]
      ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,[.TRAP]⟩ ∧
    (∀ j, j < exec.slots.length → out.2.1.slots.val[j]? = exec.slots.val[j]?)))

theorem call_host_chosen_retained {choices : Spec.SourceChoices} (occurrence : Nat) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (invariant : runtime.store.Store M → Prop)
    (shape : ∀ s, invariant s → Store.Shape view s)
    (sound : Platform.HostSound hooks invariant (Store.decodeStore view code))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : invariant store)
    (address : runtime.FuncAddr) (base : Usize) (ambient : frame) (wfAmbient : wf_frame ambient)
    (function : runtime.store.FuncInst) (identity : U64) (signature : Itasca.types.FuncType)
    (functionAt : store.funcs.val[address.index.val]? = some function)
    (host : function.code = .Host identity)
    (signatureAt : store.types.val[function.signature.val]? = some signature)
    (values : List val)
    (typed : signature.params.val.map sourceType = values.map Code.valueType)
    (arguments : ResultsTyped (Store.decodeStore view code store) (signature.params.val.map sourceType) values)
    (wellFormed : ∀ value ∈ values, wf_val value)
    (fits : ∀ value ∈ values, ResultIndexFits value)
    (represented : ValuesAt exec.slots.val base.val values)
    (sourceWf : wf_store (Store.decodeStore view code store))
    (entryTyped : Store_ok (Store.decodeStore view code store))
    (matching : ∀ p args defaults answer,
      hooks.call_host p store identity args defaults=.ok answer →
      choices.host occurrence (Store.decodeStore view code store) address.index.val identity.val
        (signature.params.val.map sourceType) (signature.results.val.map sourceType) (args.val.map sourceValue)=
          checkedHostReply memory view code answer.2.2.1 signature ⟨answer.2.2.2⟩ answer.1)
    (preserve : ∀ p args results answer,
      hooks.call_host p store identity args results = .ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀ p args results answer,
      hooks.call_host p store identity args results = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length)
    (issued : ∀ p args results answer,
      hooks.call_host p store identity args results = .ok answer →
      ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value) :
    runtime.interp.call memory hooks floats allocator exec store platform address base ⦃ out =>
      invariant out.2.2.1 ∧ FrameStorePrefix store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
      store.externs.length ≤ out.2.2.1.externs.length ∧
      ((∃ error, out.1 = .Err error ∧ HostPreparationCause allocator hooks exec store platform signature base error ∧ out.2.2.1 = store) ∨
       (ChosenHostCallSourceOutcome choices occurrence view code store ambient address values base exec out ∧
        (out.1 = .Ok () → ResultsTyped (Store.decodeStore view code out.2.2.1)
          (signature.results.val.map sourceType) (out.2.1.host_results.val.map sourceValue) ∧
          Abs.Ownership.ValuesOwned (Store.ownershipBounds out.2.2.1) (out.2.1.host_results.val.map sourceValue)))) ∧
      HostCallCauses allocator hooks exec store platform signature base identity out ⦄ := by
  have hostSource := Store.decode_host_function view code store address function identity signature functionAt host signatureAt
  apply WP.spec_mono (call_host_composition_causes memory hooks floats allocator allocation interrupts
    exec store platform address base function identity signature functionAt host signatureAt values
    typed wellFormed fits represented
    (fun out => invariant out.2.2.1 ∧ FrameStorePrefix store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
      store.externs.length ≤ out.2.2.1.externs.length ∧
      (ChosenHostCallSourceOutcome choices occurrence view code store ambient address values base exec out ∧
       (out.1 = .Ok () → ResultsTyped (Store.decodeStore view code out.2.2.1)
         (signature.results.val.map sourceType) (out.2.1.host_results.val.map sourceValue) ∧
         Abs.Ownership.ValuesOwned (Store.ownershipBounds out.2.2.1) (out.2.1.host_results.val.map sourceValue))) ∧
      HostCallCauses allocator hooks exec store platform signature base identity out) ?_)
  · intro out result
    rcases result with early | observed
    · obtain ⟨error,status,cause,unchanged⟩ := early
      exact ⟨unchanged.symm ▸ valid,unchanged.symm ▸ FrameStorePrefix.refl store,
        by rw [unchanged]; exact Spec.extend_store_refl _ sourceWf,
        by rw [unchanged],Or.inl ⟨error,status,cause,unchanged⟩,HostCallCauses.of_preparation status cause⟩
    · exact ⟨observed.1,observed.2.1,observed.2.2.1,observed.2.2.2.1,Or.inr observed.2.2.2.2.1,observed.2.2.2.2.2⟩
  · intro ready p args defaults preparation frames capacity argsEq defaultsEq
    obtain ⟨⟨status,nextPlatform,nextStore,returned⟩,callback,fresh,extension,sourceTyped⟩ :=
      sound.returned p store identity args.slice defaults.slice valid
    rw [callback,bind_ok]
    obtain ⟨nextFunction,nextFound,nextSignature⟩ := Store.host_signature_extension view code store nextStore
      address function signature functionAt signatureAt (shape nextStore fresh) extension
    have returnedIssued : ∀ value ∈ returned.val, Store.IssuedValue nextStore value := issued _ _ _ _ callback
    have selection := matching p args.slice defaults.slice _ callback
    change choices.host occurrence (Store.decodeStore view code store) address.index.val identity.val
      (signature.params.val.map sourceType) (signature.results.val.map sourceType) (args.val.map sourceValue)=
      checkedHostReply memory view code nextStore signature ⟨returned⟩ status at selection
    rw [argsEq] at selection
    step with host_resume_chosen_owned (choices:=choices) occurrence memory view code store nextStore ambient {ready with host_args := args}
      address base nextFunction signature identity.val (signature.params.val.map sourceType) values
      ⟨returned⟩ status hostSource arguments entryTyped selection extension sourceTyped wfAmbient nextFound nextSignature returnedIssued capacity
      as ⟨result,finished,hostArgs,hostResults,frameEq,executionIdentity,effect⟩
    have causes : HostCallCauses allocator hooks exec store platform signature base identity
        (result,finished,nextStore,nextPlatform) := by
      rcases effect with success | failure
      · simp only [HostCallCauses,success.1]
      · rcases failure.1 with trapped | ⟨exhausted,reply⟩
        · simp only [HostCallCauses,trapped]
        · simp only [HostCallCauses,exhausted]
          exact ⟨p,args.slice,defaults.slice,returned,by simpa only [reply] using callback⟩
    refine And.intro fresh (And.intro (preserve _ _ _ _ callback) (And.intro extension (And.intro (externs _ _ _ _ callback) (And.intro ?_ (And.intro ?_ causes)))))
    ·
      obtain ⟨padding,slotsEq,metadata⟩ := preparation
      have readyIdentity : ready.store = exec.store := by
        simpa only [] using congrArg runtime.interp.Execution.store metadata
      have oldLength : exec.slots.length ≤ ready.slots.length := by
        change exec.slots.val.length ≤ ready.slots.val.length
        rw [slotsEq,List.length_append]
        omega
      have oldSlots (j : Nat) (bound : j < exec.slots.length) : ready.slots.val[j]? = exec.slots.val[j]? := by
        rw [slotsEq,List.getElem?_append_left bound]
      refine ⟨?_,frameEq.trans frames,executionIdentity.trans readyIdentity,?_⟩
      · simpa only [hostArgs] using argsEq
      · rcases effect with success | failure
        · obtain ⟨statusEq,source,typedResults,ownedResults,valuesAt,length,preserved⟩ := success
          refine ⟨by simpa only [length] using oldLength,Or.inl ⟨statusEq,
            by simpa only [hostResults] using valuesAt,
            by simpa only [hostResults] using source,?_⟩⟩
          intro j bound outside
          have tags := Abs.results_type_of_typed typedResults
          simp only [List.map_map,Function.comp_def] at tags
          simp only [hostResults,Function.comp_def,valueType_eq_abs] at outside
          rw [tags] at outside
          exact (preserved j outside).trans (oldSlots j bound)
        · obtain ⟨statusEq,same,source⟩ := failure
          refine ⟨by simpa only [same] using oldLength,Or.inr ⟨statusEq.imp_right And.left,source,?_⟩⟩
          intro j bound
          simpa only [same] using oldSlots j bound
    · intro success
      rcases effect with returned | failed
      · exact ⟨by simpa only [hostResults] using returned.2.2.1,by simpa only [hostResults] using returned.2.2.2.1⟩
      · rcases failed.1 with trapped | ⟨exhausted,_⟩ <;> rw [success] at * <;> contradiction

end Exec.Theorems
