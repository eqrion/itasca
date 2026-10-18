import Exec.Theorems.Host.HostCallContext
import Exec.Abs.Indirect.HostSimulation
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- The checked atomic host event composes with source call resolution and
all surrounding contexts. This retains a positive source step count. -/
theorem HostCallSourceOutcome.indirect_frame_events {M P : Type}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (before : runtime.store.Store M) (ambient : frame) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr) (table type position : Nat)
    (address : runtime.FuncAddr) (front args : List val) (base : Usize)
    (exec : runtime.interp.Execution)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P)
    (observed : HostCallSourceOutcome view code before f.toFrame address args base exec out)
    (storeWf : wf_store (Store.decodeStore view code before))
    (freshWf : wf_store (Store.decodeStore view code out.2.2.1))
    (ambientWf : wf_frame ambient) (frameWf : wf_frame f.toFrame)
    (labels : Abs.LabelsWf f.labels) (values : Forall wf_val front)
    (tail : Forall wf_instr after) (callers : Forall Abs.FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (resolve : Spec.IndirectTarget (Store.decodeStore view code before) f.toFrame table type position address.index.val)
    (tableBound : table < 2^32) (typeBound : type < 2^32) (positionBound : position < 2^32)
    (argsWf : Forall wf_val args) :
    ∃ n, 2 ≤ n ∧ Spec.StepsHN n
      (Abs.decode ⟨Store.decodeStore view code before,ambient,
        {f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type) :: after,vals := front ++ args ++ [Abs.integerVal .I32 position]} :: rest,[]⟩)
      (hostCallEvents address out) (hostCallFrameResult view code ambient f rest after front out) := by
  obtain ⟨arguments,_,_,_,outcome⟩ := observed
  rcases outcome with ⟨success,_,source,_⟩ | ⟨failure,source,_⟩
  · refine ⟨2,by omega,?_⟩
    simpa only [hostCallEvents,hostCallFrameResult,success,arguments] using
      Abs.Indirect.host_return_simulation _ _ ambient f rest after table type position address.index.val front args
        (out.2.1.host_results.val.map sourceValue) _ storeWf ambientWf frameWf labels values tail callers
        heights resolve tableBound typeBound positionBound argsWf source
  · obtain ⟨n,bound,trace⟩ := Abs.Indirect.host_trap_simulation _ _ ambient f rest after table type position address.index.val
      front args _ storeWf freshWf ambientWf frameWf labels values tail callers heights resolve tableBound typeBound positionBound argsWf source
    refine ⟨n,bound,?_⟩
    rcases failure with trapped | exhausted
    · simpa only [hostCallEvents,hostCallFrameResult,trapped,arguments] using trace
    · simpa only [hostCallEvents,hostCallFrameResult,exhausted,arguments] using trace
/-- The actual extracted host call, including preparation and result checking,
refines an indirect source call under every suspended execution context. -/
theorem call_indirect_host_frame_source {M P F A : Type}
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
    (sourceWf : ∀ s, invariant s → wf_store (Store.decodeStore view code s))
    (address : runtime.FuncAddr) (base : Usize) (ambient : frame) (wfAmbient : wf_frame ambient)
    (function : runtime.store.Function) (identity : U64) (signature : Itasca.types.FuncType)
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
      ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value)
    (f : Abs.AFrame) (frameWf : wf_frame f.toFrame)
    (rest : List Abs.AFrame) (after : List instr) (table type position : Nat) (front : List val)
    (labels : Abs.LabelsWf f.labels) (frontWf : Forall wf_val front)
    (tail : Forall wf_instr after) (callers : Forall Abs.FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (resolve : Spec.IndirectTarget (Store.decodeStore view code store) f.toFrame table type position address.index.val)
    (tableBound : table < 2^32) (typeBound : type < 2^32) (positionBound : position < 2^32) :
    runtime.interp.call memory hooks floats allocator exec store platform address base ⦃ out =>
      invariant out.2.2.1 ∧
      ((∃ error, out.1 = .Err error ∧ HostPreparationError error ∧ out.2.2.1 = store) ∨
       (HostCallSourceOutcome view code store f.toFrame address values base exec out ∧
        ∃ n, 2 ≤ n ∧ Spec.StepsHN n
          (Abs.decode ⟨Store.decodeStore view code store,ambient,
            {f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type) :: after,vals := front ++ values ++ [Abs.integerVal .I32 position]} :: rest,[]⟩)
          (hostCallEvents address out) (hostCallFrameResult view code ambient f rest after front out))) ⦄ := by
  apply WP.spec_mono (call_host_source memory hooks floats allocator allocation interrupts view code
    invariant shape sound exec store platform valid address base f.toFrame frameWf function identity signature
    functionAt host signatureAt values typed arguments wellFormed fits represented issued)
  intro out observed
  obtain ⟨fresh,early | called⟩ := observed
  · exact ⟨fresh,Or.inl early⟩
  · exact ⟨fresh,Or.inr ⟨called,called.indirect_frame_events view code store ambient f rest after table type position address front values
      base exec out (sourceWf store valid) (sourceWf _ fresh) wfAmbient frameWf labels frontWf tail callers
      heights resolve tableBound typeBound positionBound wellFormed⟩⟩
end Exec.Theorems
