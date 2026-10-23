import Exec.Theorems.Host.HostIndirectContext
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- The actual extracted host call, including preparation and result checking,
refines an indirect source call under every suspended execution context. -/
theorem recorded_indirect_host_frame_source {M P F A : Type}
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
      ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value)
    (f : Abs.AFrame) (frameWf : wf_frame f.toFrame)
    (rest : List Abs.AFrame) (after : List instr) (table type position : Nat) (front : List val)
    (labels : Abs.LabelsWf f.labels) (frontWf : Forall wf_val front)
    (tail : Forall wf_instr after) (callers : Forall Abs.FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (resolve : Spec.IndirectTarget (Store.decodeStore view code store) f.toFrame table type position address.index.val)
    (tableBound : table < 2^32) (typeBound : type < 2^32) (positionBound : position < 2^32) (prior : List HostEvent) :
    recordedHostCall memory hooks floats allocator exec store platform address base prior ⦃ (out,trace) =>
      invariant out.2.2.1 ∧ trace = prior ++ hostCallEvents address out ∧
      ((∃ error, out.1 = .Err error ∧ HostPreparationError error ∧ out.2.2.1 = store) ∨
       (HostCallSourceOutcome view code store f.toFrame address values base exec out ∧
        ∃ n, 2 ≤ n ∧ Spec.StepsHN n
          (Abs.decode ⟨Store.decodeStore view code store,ambient,
            {f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type) :: after,vals := front ++ values ++ [Abs.integerVal .I32 position]} :: rest,[]⟩)
          (hostCallEvents address out) (hostCallFrameResult view code ambient f rest after front out))) ⦄ := by
  unfold recordedHostCall Platform.Recording.run
  step with call_indirect_host_frame_source memory hooks floats allocator allocation interrupts view code
    invariant shape sound exec store platform valid sourceWf address base ambient wfAmbient
    function identity signature functionAt host signatureAt values typed arguments wellFormed fits represented issued
    f frameWf rest after table type position front labels frontWf tail callers heights resolve
    tableBound typeBound positionBound as ⟨out,fresh,outcome⟩
  exact ⟨fresh,outcome⟩
end Exec.Theorems
