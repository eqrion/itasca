import Exec.Theorems.Invocation.InvokeHost
import Exec.Interp.Invocation.InvokeCheckedTotal
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Argument rejection precedes the callback and preserves all API state.
Accepted calls retain the explicit conditional host contract and exact readback. -/
theorem invoke_host_checked {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (invariant : runtime.store.Store M → Prop)
    (shape : ∀ s, invariant s → Store.Shape view s)
    (sound : Platform.HostSound hooks invariant (Store.decodeStore view code))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : invariant store) (sourceWf : wf_store (Store.decodeStore view code store))
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.Function) (identity : U64)
    (signature : Itasca.types.FuncType) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (functionAt : store.funcs.val[address.index.val]? = some function)
    (host : function.code = .Host identity)
    (signatureAt : store.types.val[function.signature.val]? = some signature)
    (issuedArgs : ∀ value ∈ args.val, Store.IssuedValue store value)
    (preserve : ∀ p arguments defaults answer,
      hooks.call_host p store identity arguments defaults = .ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀ p arguments defaults answer,
      hooks.call_host p store identity arguments defaults = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length)
    (issued : ∀ p arguments defaults answer,
      hooks.call_host p store identity arguments defaults = .ok answer →
      ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results ⦃ out =>
      (∃ error, runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Err error) ∧
        out = (.Err error,exec,store,platform,results)) ∨ (
      (invariant out.2.2.1 ∧ FrameStorePrefix store out.2.2.1 ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
        store.externs.length ≤ out.2.2.1.externs.length) ∧
      (out.1 = .Ok () →
        ResultsTyped (Store.decodeStore view code out.2.2.1) (signature.results.val.map sourceType)
          (out.2.2.2.2.val.map sourceValue) ∧
        Abs.Ownership.ValuesOwned (Store.ownershipBounds out.2.2.1) (out.2.2.2.2.val.map sourceValue) ∧
        StepH ⟨⟨Store.decodeStore view code store,ambient⟩, vals (args.val.map sourceValue) ++ [.CALL_ADDR address.index.val]⟩
          [.call address.index.val (args.val.map sourceValue) (some (out.2.2.2.2.val.map sourceValue))]
          ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩, vals (out.2.2.2.2.val.map sourceValue)⟩ ∧
        (∀ value ∈ out.2.2.2.2.val, Store.ValueInStore out.2.2.1 value)) ∧
      (∀ error, out.1 = .Err error →
        InvocationResourceCause allocator exec store signature results error ∨
        ∃ prepared p called,
          prepared.frames.val = [] ∧ ValuesAt prepared.slots.val 0 (args.val.map sourceValue) ∧
          runtime.interp.call memory hooks floats allocator prepared store p address 0#usize = .ok called ∧
          called.1 = .Err error ∧ called.2.2.1 = out.2.2.1 ∧
          HostCallCauses allocator hooks prepared store p signature 0#usize identity called ∧
          ((∃ rejected, called.1 = .Err rejected ∧
              HostPreparationCause allocator hooks prepared store p signature 0#usize rejected ∧ called.2.2.1 = store) ∨
            HostCallSourceOutcome view code store ambient address (args.val.map sourceValue) 0#usize prepared called))) ⦄ := by
  apply WP.spec_mono (invoke_with_checked_outcome_total memory hooks floats allocator exec store platform
    address function signature args results owner functionAt signatureAt
    (fun out => 
      (invariant out.2.2.1 ∧ FrameStorePrefix store out.2.2.1 ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
        store.externs.length ≤ out.2.2.1.externs.length) ∧
      (out.1 = .Ok () →
        ResultsTyped (Store.decodeStore view code out.2.2.1) (signature.results.val.map sourceType)
          (out.2.2.2.2.val.map sourceValue) ∧
        Abs.Ownership.ValuesOwned (Store.ownershipBounds out.2.2.1) (out.2.2.2.2.val.map sourceValue) ∧
        StepH ⟨⟨Store.decodeStore view code store,ambient⟩, vals (args.val.map sourceValue) ++ [.CALL_ADDR address.index.val]⟩
          [.call address.index.val (args.val.map sourceValue) (some (out.2.2.2.2.val.map sourceValue))]
          ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩, vals (out.2.2.2.2.val.map sourceValue)⟩ ∧
        (∀ value ∈ out.2.2.2.2.val, Store.ValueInStore out.2.2.1 value)) ∧
      (∀ error, out.1 = .Err error →
        InvocationResourceCause allocator exec store signature results error ∨
        ∃ prepared p called,
          prepared.frames.val = [] ∧ ValuesAt prepared.slots.val 0 (args.val.map sourceValue) ∧
          runtime.interp.call memory hooks floats allocator prepared store p address 0#usize = .ok called ∧
          called.1 = .Err error ∧ called.2.2.1 = out.2.2.1 ∧
          HostCallCauses allocator hooks prepared store p signature 0#usize identity called ∧
          ((∃ rejected, called.1 = .Err rejected ∧
              HostPreparationCause allocator hooks prepared store p signature 0#usize rejected ∧ called.2.2.1 = store) ∨
            HostCallSourceOutcome view code store ambient address (args.val.map sourceValue) 0#usize prepared called)))
    (fun accepted => by
      have checked := Store.check_values_source_typed memory view code store sourceWf args
        (alloc.vec.Vec.deref signature.params) issuedArgs
      rw [accepted] at checked
      simp only [WP.spec_ok] at checked
      exact invoke_host_outcomes memory hooks floats allocator allocation interrupts view code
        invariant shape sound exec store platform valid sourceWf ambient ambientWf address function identity
        signature args results owner functionAt host signatureAt (checked trivial).2.1 accepted preserve externs issued))
  intro out observed
  exact observed.elim Or.inl (fun entered => Or.inr entered.2)
end Exec.Theorems
