import Exec.Theorems.Host.HostResumeOwned
import Exec.Theorems.Host.HostCallFrames
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- A suspended, already prepared host call resumes with its exact slot/frame
transport and typed owned results on success. The raw reply is dynamically
checked; no callback implementation or callback-normality law is assumed. -/
theorem prepared_resume_source {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (before after : runtime.store.Store M) (ambient : frame)
    (exec padded : runtime.interp.Execution) (address : runtime.FuncAddr) (base : Usize)
    (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (identity : Nat) (params : List valtype) (arguments : List val)
    (args values : alloc.vec.Vec runtime.Value) (status : core.result.Result Unit runtime.platform.HostError)
    (host : HostFunction (Store.decodeStore view code before) address.index.val identity params (signature.results.val.map sourceType))
    (argumentsTyped : ResultsTyped (Store.decodeStore view code before) params arguments)
    (extension : Extend_store (Store.decodeStore view code before) (Store.decodeStore view code after))
    (sourceTyped : Store_ok (Store.decodeStore view code after)) (ambientWf : wf_frame ambient)
    (functionAt : after.funcs.val[address.index.val]?=some function)
    (signatureAt : after.types.val[function.signature.val]?=some signature)
    (issued : ∀value∈values.val,Store.IssuedValue after value)
    (preparation : ∃padding,SlotsEffect exec padded (exec.slots.val++padding))
    (frames : padded.frames=exec.frames)
    (capacity : base.val+Code.slots (signature.results.val.map sourceType)≤padded.slots.length)
    (copied : args.val.map sourceValue=arguments) :
    hostResume memory {padded with host_args:=args} after address base values status ⦃out=>
      HostCallSourceOutcome view code before ambient address arguments base exec (out.1,out.2,after,()) ∧
      (out.1=.Ok () → ResultsTyped (Store.decodeStore view code after) (signature.results.val.map sourceType)
        (out.2.host_results.val.map sourceValue) ∧
        Abs.Ownership.ValuesOwned (Store.ownershipBounds after) (out.2.host_results.val.map sourceValue))⦄ := by
  apply WP.spec_mono (host_resume_source_owned memory view code before after ambient {padded with host_args:=args}
    address base function signature identity params arguments values status host argumentsTyped extension sourceTyped ambientWf
    functionAt signatureAt issued capacity)
  rintro ⟨result,finished⟩ ⟨hostArgs,hostResults,frameEq,executionIdentity,effect⟩
  dsimp only at hostArgs hostResults frameEq executionIdentity effect ⊢
  obtain ⟨padding,slotsEq,metadata⟩ := preparation
  have paddedIdentity : padded.store=exec.store := by
    have projected:=congrArg runtime.interp.Execution.store metadata
    exact projected
  have oldLength : exec.slots.length≤padded.slots.length := by
    change exec.slots.val.length≤padded.slots.val.length
    rw [slotsEq,List.length_append]
    omega
  have oldSlots (j : Nat) (bound : j<exec.slots.length) : padded.slots.val[j]?=exec.slots.val[j]? := by
    rw [slotsEq,List.getElem?_append_left bound]
  constructor
  · refine ⟨?_,frameEq.trans frames,executionIdentity.trans paddedIdentity,?_⟩
    · simpa only [hostArgs] using copied
    · rcases effect with success|failure
      · obtain ⟨statusEq,source,typed,owned,represented,length,preserved⟩ := success
        refine ⟨by simpa only [length] using oldLength,Or.inl ⟨statusEq,?_,?_,?_⟩⟩
        · simpa only [hostResults] using represented
        · simpa only [hostResults] using source
        · intro j bound outside
          have tags := Abs.results_type_of_typed typed
          simp only [List.map_map,Function.comp_def] at tags
          simp only [hostResults,Function.comp_def,valueType_eq_abs] at outside
          rw [tags] at outside
          exact (preserved j outside).trans (oldSlots j bound)
      · obtain ⟨statusEq,same,source⟩ := failure
        refine ⟨by simpa only [same] using oldLength,Or.inr ⟨statusEq.imp_right And.left,source,?_⟩⟩
        intro j bound
        simpa only [same] using oldSlots j bound
  · intro ok
    rcases effect with success|failure
    · exact ⟨by simpa only [hostResults] using success.2.2.1,by simpa only [hostResults] using success.2.2.2.1⟩
    · rcases failure.1 with trapped|⟨exhausted,stack⟩ <;> rw [ok] at * <;> contradiction
end Exec.Theorems.OpenReentrantControl
