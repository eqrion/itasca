import Exec.Theorems.Host.Open.Driver.PreparedStructuredResumeAt
import Exec.Theorems.Host.Open.Driver.ResumeReply
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.StructuredMachine

/-- The captured source context and native structured continuation agree at
exactly the reached code world after dynamic reply checking. -/
theorem prepared_source_resume_at {M : Type}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {ambient : frame} {f : Abs.AFrame} {rest : List Abs.AFrame} {op : instr} {after : List instr}
    {expected : List valtype} {sourcePC : Nat} {pendingFlag : Bool}
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := op::after}::rest,[]⟩ expected sourcePC pendingFlag)
    {raw : runtime.interp.Frame} {frameIndex : Usize} {pc : U32}
    (last : frameIndex.val+1=exec.frames.length)
    (lookup : exec.frames.val[frameIndex.val]?=some raw)
    (binding : FrameBinding store exec raw f) (slots : FrameSlots exec raw f)
    {compiled C targets next output}
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Store.decodeStore view code store) raw
      {f with code := op::after} compiled C targets next output)
    {front args consumed : List val} {returns : List valtype} {address : runtime.FuncAddr} {base : Usize}
    (split : f.vals=front++consumed)
    (destination : base.val=raw.base.val+Code.slots ((f.locals++front).map Code.valueType))
    (heights : ∀ label∈f.labels, label.height≤front.length)
    (continuation : Code.StructuredCode (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Code.valueType++returns) after pc.val next output)
    (pending : Abs.HostPending
      ⟨Store.decodeStore view code store,ambient,{f with code := after,vals := front}::rest,[]⟩ returns)
    (memory : runtime.platform.MemoryBuffer M)
    (padded : runtime.interp.Execution) (freshStore : runtime.store.Store M)
    (afterCode : Store.CodeInterpretation) (agrees : Store.CodeAgreesOn store code afterCode)
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
    (extension : Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode freshStore))
    (sourceTyped : Store_ok (Store.decodeStore view afterCode freshStore))
    (fresh : CertifiedSupportedStore view afterCode freshStore)
    (sourcePending : Spec.OpenHost.Pending)
    (completion : ∀fresh returned,sourcePending.completed ⟨fresh,some returned⟩=
      Abs.decode ⟨fresh,ambient,{f with code:=after,vals:=front++returned}::rest,[]⟩) :
    hostResume memory {padded with host_args:=copied} freshStore address base values status ⦃out=>
      HostCallSourceOutcome view afterCode store f.toFrame address args base
        {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} (out.1,out.2,freshStore,()) ∧
      (out.1=.Ok () → ∃finalPC,Execution view afterCode freshStore out.2
        ⟨Store.decodeStore view afterCode freshStore,ambient,
          {f with code:=after,vals:=front++out.2.host_results.val.map sourceValue}::rest,[]⟩ expected finalPC false ∧
        Abs.Ownership.ValuesOwned (Store.ownershipBounds freshStore) (out.2.host_results.val.map sourceValue) ∧
        Abs.decode ⟨Store.decodeStore view afterCode freshStore,ambient,
          {f with code:=after,vals:=front++out.2.host_results.val.map sourceValue}::rest,[]⟩=
          sourcePending.completed (checkedHostReply memory view afterCode freshStore signature values status))⦄ := by
  obtain ⟨out,actual,source,resumption⟩ := WP.spec_imp_exists
    (prepared_structured_resume_at machine last lookup binding slots program point split destination heights continuation pending
      memory padded freshStore afterCode agrees function signature identity params copied values status host argumentsTyped
      resultTypes frameWf functionAt signatureAt issued preparation frames capacity argumentsEq retained bounds extension sourceTyped fresh)
  rw [actual,WP.spec_ok]
  refine ⟨source,?_⟩
  intro successful
  obtain ⟨finalPC,resumed,owned⟩ := resumption successful
  refine ⟨finalPC,resumed,owned,?_⟩
  have replyResult := host_resume_checked_result memory view afterCode freshStore {padded with host_args:=copied}
    address base function signature functionAt signatureAt values status out actual successful
  have replyEq : checkedHostReply memory view afterCode freshStore signature values status=
      ⟨Store.decodeStore view afterCode freshStore,(checkedHostReply memory view afterCode freshStore signature values status).result⟩ := rfl
  rw [replyEq,replyResult,completion]
end Exec.Theorems.OpenReentrantControl
