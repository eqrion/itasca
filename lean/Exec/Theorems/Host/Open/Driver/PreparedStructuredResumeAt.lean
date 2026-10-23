import Exec.Theorems.Host.Open.Driver.PreparedStructuredResume
import Exec.Theorems.Composition.ExecutionCode
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.StructuredMachine

/-- Successful native resumption retains the exact post-callback code world,
including code keys published during arbitrarily nested host interaction. -/
theorem prepared_structured_resume_at {M : Type} {emission : FunctionEmission} {allowed : instr → Prop}
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
    (fresh : CertifiedSupportedStore emission allowed view afterCode freshStore) :
    hostResume memory {padded with host_args:=copied} freshStore address base values status ⦃out=>
      HostCallSourceOutcome view afterCode store f.toFrame address args base
        {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} (out.1,out.2,freshStore,()) ∧
      (out.1=.Ok () → ∃finalPC,Execution emission (Abs.SupportedState allowed) view afterCode freshStore out.2
        ⟨Store.decodeStore view afterCode freshStore,ambient,
          {f with code:=after,vals:=front++out.2.host_results.val.map sourceValue}::rest,[]⟩ expected finalPC false ∧
        Abs.Ownership.ValuesOwned (Store.ownershipBounds freshStore) (out.2.host_results.val.map sourceValue))⦄ := by
  have decoded := Store.decodeStore_code_agrees view agrees
  have machine' : Execution emission (Abs.SupportedState allowed) view afterCode store exec
      ⟨Store.decodeStore view afterCode store,ambient,{f with code:=op::after}::rest,[]⟩ expected sourcePC pendingFlag := by
    simpa only [decoded] using machine.change_code agrees
  have point' : FramePoint emission (Store.decodeStore view afterCode store) raw
      {f with code:=op::after} compiled C targets next output := by simpa only [decoded] using point
  have pending' : Abs.HostPending
      ⟨Store.decodeStore view afterCode store,ambient,{f with code:=after,vals:=front}::rest,[]⟩ returns := by
    simpa only [decoded] using pending
  have host' : HostFunction (Store.decodeStore view afterCode store) address.index.val identity params
      (signature.results.val.map sourceType) := by simpa only [decoded] using host
  have arguments' : ResultsTyped (Store.decodeStore view afterCode store) params args := by simpa only [decoded] using argumentsTyped
  have extension' : Extend_store (Store.decodeStore view afterCode store) (Store.decodeStore view afterCode freshStore) := by
    simpa only [decoded] using extension
  exact prepared_structured_resume machine' last lookup binding slots program point' split destination heights continuation pending'
    memory padded freshStore function signature identity params copied values status host' arguments' resultTypes frameWf
    functionAt signatureAt issued preparation frames capacity argumentsEq retained bounds extension' sourceTyped fresh
end Exec.Theorems.OpenReentrantControl
