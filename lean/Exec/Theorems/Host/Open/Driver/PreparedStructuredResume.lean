import Exec.Theorems.Host.Open.Driver.PreparedResume
import Exec.Theorems.Host.HostStructuredResume
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.StructuredMachine

/-- A prepared host continuation reconstructs the exact typed abstract caller
on every dynamically successful reply. Permissions are discharged by the native
resume proof, with no callback-normality or assumed simulation premise. -/
theorem prepared_structured_resume {M : Type} {emission : FunctionEmission} {allowed : instr → Prop}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {ambient : frame} {f : Abs.AFrame} {rest : List Abs.AFrame} {op : instr} {after : List instr}
    {expected : List valtype} {sourcePC : Nat} {pendingFlag : Bool}
    (machine : Execution emission (Abs.SupportedState allowed) view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := op::after}::rest,[]⟩ expected sourcePC pendingFlag)
    {raw : runtime.interp.Frame} {frameIndex : Usize} {pc : U32}
    (last : frameIndex.val+1=exec.frames.length)
    (lookup : exec.frames.val[frameIndex.val]?=some raw)
    (binding : FrameBinding store exec raw f) (slots : FrameSlots exec raw f)
    {compiled C targets next output}
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint emission (Store.decodeStore view code store) raw
      {f with code := op::after} compiled C targets next output)
    {front args consumed : List val} {returns : List valtype} {address : runtime.FuncAddr} {base : Usize}
    (split : f.vals=front++consumed)
    (destination : base.val=raw.base.val+Code.slots ((f.locals++front).map Code.valueType))
    (heights : ∀ label∈f.labels, label.height≤front.length)
    (continuation : Code.StructuredCodeWithTables (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Code.valueType++returns) after pc.val next output)
    (pending : Abs.HostPending
      ⟨Store.decodeStore view code store,ambient,{f with code := after,vals := front}::rest,[]⟩ returns)
    (memory : runtime.platform.MemoryBuffer M)
    (padded : runtime.interp.Execution) (freshStore : runtime.store.Store M)
    (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (identity : Nat) (params : List valtype) (copied values : alloc.vec.Vec runtime.Value)
    (status : core.result.Result Unit runtime.platform.HostError)
    (host : HostFunction (Store.decodeStore view code store) address.index.val identity params
      (signature.results.val.map sourceType))
    (argumentsTyped : ResultsTyped (Store.decodeStore view code store) params args)
    (resultTypes : signature.results.val.map sourceType=returns)
    (frameWf : wf_frame f.toFrame)
    (functionAt : freshStore.funcs.val[address.index.val]?=some function)
    (signatureAt : freshStore.types.val[function.signature.val]?=some signature)
    (issued : ∀value∈values.val,Store.IssuedValue freshStore value)
    (preparation : ∃padding,SlotsEffect {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} padded
      (exec.slots.val++padding))
    (frames : padded.frames=(exec.frames.set frameIndex {raw with pc:=pc}))
    (capacity : base.val+Code.slots (signature.results.val.map sourceType)≤padded.slots.length)
    (argumentsEq : copied.val.map sourceValue=args)
    (retained : FrameStorePrefix store freshStore) (bounds : FrameTypeBounds store)
    (extension : Extend_store (Store.decodeStore view code store) (Store.decodeStore view code freshStore))
    (sourceTyped : Store_ok (Store.decodeStore view code freshStore))
    (fresh : CertifiedSupportedStore emission allowed view code freshStore) :
    hostResume memory {padded with host_args:=copied} freshStore address base values status ⦃out=>
      HostCallSourceOutcome view code store f.toFrame address args base
        {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} (out.1,out.2,freshStore,()) ∧
      (out.1=.Ok () → ∃finalPC,Execution emission (Abs.SupportedState allowed) view code freshStore out.2
        ⟨Store.decodeStore view code freshStore,ambient,
          {f with code:=after,vals:=front++out.2.host_results.val.map sourceValue}::rest,[]⟩ expected finalPC false ∧
        Abs.Ownership.ValuesOwned (Store.ownershipBounds freshStore) (out.2.host_results.val.map sourceValue))⦄ := by
  apply WP.spec_mono (prepared_resume_source memory view code store freshStore f.toFrame
    {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} padded address base function signature identity params args
    copied values status host argumentsTyped extension sourceTyped frameWf functionAt signatureAt issued preparation frames capacity argumentsEq)
  intro out post
  refine ⟨post.1,?_⟩
  intro ok
  have typed : ResultsTyped (Store.decodeStore view code freshStore) returns (out.2.host_results.val.map sourceValue) := by
    simpa only [resultTypes] using (post.2 ok).1
  obtain ⟨finalPC,resumed⟩ := host_structured_resume machine last lookup binding slots program point split destination heights continuation
    pending post.1 ok retained bounds extension fresh typed
  exact ⟨finalPC,resumed,(post.2 ok).2⟩
end Exec.Theorems.OpenReentrantControl
