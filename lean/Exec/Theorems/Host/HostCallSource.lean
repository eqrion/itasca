import Exec.Interp.Control.StructuredPoint
import Exec.Interp.Host.HostCallCompose
import Exec.Theorems.Host.HostResume
import Exec.Store.Invariant.HostSignature
import Exec.Platform.HostSound

namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Observable behavior after an actual host callback. Preparation rejections
are separated by the calling theorem because they perform no host event. -/
def HostCallSourceOutcome {M P : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (before : runtime.store.Store M) (ambient : frame) (address : runtime.FuncAddr)
    (args : List val) (base : Usize) (exec : runtime.interp.Execution)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : Prop :=
  out.2.1.host_args.val.map sourceValue = args ∧ out.2.1.frames = exec.frames ∧ out.2.1.store = exec.store ∧
  exec.slots.length ≤ out.2.1.slots.length ∧
  ((out.1 = .Ok () ∧
    ValuesAt out.2.1.slots.val base.val (out.2.1.host_results.val.map sourceValue) ∧
    StepH ⟨⟨Store.decodeStore view code before,ambient⟩,vals args ++ [.CALL_ADDR address.index.val]⟩
      [.call address.index.val args (some (out.2.1.host_results.val.map sourceValue))]
      ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,vals (out.2.1.host_results.val.map sourceValue)⟩ ∧
    (∀ j, j < exec.slots.length →
      j < base.val ∨ base.val + Code.slots (out.2.1.host_results.val.map (Code.valueType ∘ sourceValue)) ≤ j →
      out.2.1.slots.val[j]? = exec.slots.val[j]?)) ∨
   ((out.1 = .Err (.Trap .Host) ∨ out.1 = .Err (.Exhausted .CallStack)) ∧
    StepH ⟨⟨Store.decodeStore view code before,ambient⟩,vals args ++ [.CALL_ADDR address.index.val]⟩
      [.call address.index.val args none]
      ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,[.TRAP]⟩ ∧
    (∀ j, j < exec.slots.length → out.2.1.slots.val[j]? = exec.slots.val[j]?)))

/-- Actual resource causes for a host call, including a callback's explicit
stack-overflow reply. The checked callback equation retains its returned store. -/
def HostCallCauses {A M P : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (signature : Itasca.types.FuncType)
    (base : Usize) (identity : U64)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : Prop :=
  match out.1 with
  | .Ok _ | .Err (.Trap _) => True
  | .Err (.Exhausted .CallStack) =>
      ∃ p args defaults returned, hooks.call_host p store identity args defaults =
        .ok (.Err .StackOverflow,out.2.2.2,out.2.2.1,returned)
  | .Err error => HostPreparationCause allocator hooks exec store platform signature base error

theorem HostCallCauses.of_preparation {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {signature : Itasca.types.FuncType}
    {base : Usize} {identity : U64}
    {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}
    {error : runtime.ExecError} (status : out.1 = .Err error)
    (cause : HostPreparationCause allocator hooks exec store platform signature base error) :
    HostCallCauses allocator hooks exec store platform signature base identity out := by
  simp only [HostCallCauses,status]
  cases error <;> simp_all [HostPreparationCause]
  rename_i limit
  cases limit <;> simp_all [HostPreparationCause]

/-- The actual extracted host call either rejects during preparation without
changing the store, or performs its checked atomic source host event. Issued
result references express handle provenance, not assumed result typing. -/
theorem call_host_source_causes {M P F A : Type}
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
    (issued : ∀ p args results answer,
      hooks.call_host p store identity args results = .ok answer →
      ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value) :
    runtime.interp.call memory hooks floats allocator exec store platform address base ⦃ out =>
      invariant out.2.2.1 ∧
      ((∃ error, out.1 = .Err error ∧ HostPreparationCause allocator hooks exec store platform signature base error ∧ out.2.2.1 = store) ∨
       HostCallSourceOutcome view code store ambient address values base exec out) ∧
      HostCallCauses allocator hooks exec store platform signature base identity out ⦄ := by
  have hostSource := Store.decode_host_function view code store address function identity signature functionAt host signatureAt
  apply WP.spec_mono (call_host_composition_causes memory hooks floats allocator allocation interrupts
    exec store platform address base function identity signature functionAt host signatureAt values
    typed wellFormed fits represented
    (fun out => invariant out.2.2.1 ∧ HostCallSourceOutcome view code store ambient address values base exec out ∧
      HostCallCauses allocator hooks exec store platform signature base identity out) ?_)
  · intro out result
    rcases result with early | observed
    · obtain ⟨error,status,cause,unchanged⟩ := early
      exact ⟨unchanged.symm ▸ valid,Or.inl ⟨error,status,cause,unchanged⟩,HostCallCauses.of_preparation status cause⟩
    · exact ⟨observed.1,Or.inr observed.2.1,observed.2.2⟩
  · intro ready p args defaults preparation frames capacity argsEq defaultsEq
    obtain ⟨⟨status,nextPlatform,nextStore,returned⟩,callback,fresh,extension,sourceTyped⟩ :=
      sound.returned p store identity args.slice defaults.slice valid
    rw [callback,bind_ok]
    obtain ⟨nextFunction,nextFound,nextSignature⟩ := Store.host_signature_extension view code store nextStore
      address function signature functionAt signatureAt (shape nextStore fresh) extension
    have returnedIssued : ∀ value ∈ returned.val, Store.IssuedValue nextStore value := issued _ _ _ _ callback
    step with host_resume_source memory view code store nextStore ambient {ready with host_args := args}
      address base nextFunction signature identity.val (signature.params.val.map sourceType) values
      ⟨returned⟩ status hostSource arguments extension sourceTyped wfAmbient nextFound nextSignature returnedIssued capacity
      as ⟨result,finished,hostArgs,hostResults,frameEq,executionIdentity,effect⟩
    have causes : HostCallCauses allocator hooks exec store platform signature base identity
        (result,finished,nextStore,nextPlatform) := by
      rcases effect with success | failure
      · simp only [HostCallCauses,success.1]
      · rcases failure.1 with trapped | ⟨exhausted,reply⟩
        · simp only [HostCallCauses,trapped]
        · simp only [HostCallCauses,exhausted]
          exact ⟨p,args.slice,defaults.slice,returned,by simpa only [reply] using callback⟩
    refine ⟨fresh,?_,causes⟩
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
      · obtain ⟨statusEq,source,typedResults,valuesAt,length,preserved⟩ := success
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
/-- The actual extracted host call either rejects during preparation without
changing the store, or performs its checked atomic source host event. Issued
result references express handle provenance, not assumed result typing. -/
theorem call_host_source {M P F A : Type}
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
    (issued : ∀ p args results answer,
      hooks.call_host p store identity args results = .ok answer →
      ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value) :
    runtime.interp.call memory hooks floats allocator exec store platform address base ⦃ out =>
      invariant out.2.2.1 ∧
      ((∃ error, out.1 = .Err error ∧ HostPreparationError error ∧ out.2.2.1 = store) ∨
       HostCallSourceOutcome view code store ambient address values base exec out) ⦄ := by

  apply WP.spec_mono (call_host_source_causes memory hooks floats allocator allocation interrupts
    view code invariant shape sound exec store platform valid address base ambient wfAmbient
    function identity signature functionAt host signatureAt values typed arguments wellFormed fits represented issued)
  rintro out ⟨fresh,early | observed,causes⟩
  · obtain ⟨error,status,cause,unchanged⟩ := early
    exact ⟨fresh,Or.inl ⟨error,status,cause.error,unchanged⟩⟩
  · exact ⟨fresh,Or.inr observed⟩
end Exec.Theorems
