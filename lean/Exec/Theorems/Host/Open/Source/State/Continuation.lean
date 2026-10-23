import Exec.Theorems.Host.Open.Source.State.ResumeAt
import Exec.Theorems.Host.HostOwnership
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp SpecExt Exec.Interp.StructuredMachine

/-- A saved native caller is related to one particular source context at every
future checked world, including newly published code. This contract concerns
resumption, and never assumes that the intervening host control returns. -/
def SourceContinuation {M : Type} (emission : FunctionEmission) (allowed : instr → Prop)
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (ready : runtime.interp.Execution) (address : runtime.FuncAddr) (base : Usize)
    (sourcePending : Spec.OpenHost.Pending) (expected : List valtype) : Prop :=
  ∃function signature,store.funcs.val[address.index.val]?=some function ∧
    store.types.val[function.signature.val]?=some signature ∧
    ∀afterCode freshStore,Store.CodeAgreesOn store code afterCode → FrameStorePrefix store freshStore →
      store.externs.length≤freshStore.externs.length →
      FrameTypeBounds store →
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode freshStore) →
      Store_ok (Store.decodeStore view afterCode freshStore) →
      CertifiedSupportedStore emission allowed view afterCode freshStore →
      ∀values status,(∀value∈values.val,Store.IssuedValue freshStore value) →
      hostResume memory ready freshStore address base values status ⦃out=>out.1=.Ok () →
        ∃source finalPC pendingFlag,Execution emission (Abs.SupportedState allowed) view afterCode freshStore out.2
          source expected finalPC pendingFlag ∧
          Abs.Ownership.StatefulOwned (Store.ownershipBounds freshStore) source ∧
          Abs.decode source=sourcePending.completed (checkedHostReply memory view afterCode freshStore signature values status)⦄

/-- The saved-context contract is constructed from native frame, slot and code
certificates and the independently derived source-context completion equation. -/
theorem source_continuation_of_prepared {M : Type}
    {emission : FunctionEmission}
    {allowed : instr → Prop}
    {view : M → Slice U8}
    {code : Store.CodeInterpretation}
    {store : runtime.store.Store M}
    {exec : runtime.interp.Execution}
    {ambient : frame}
    {f : Abs.AFrame}
    {rest : List Abs.AFrame}
    {op : instr}
    {after : List instr}
    {expected : List valtype}
    {sourcePC : Nat}
    {pendingFlag : Bool}
    (machine : Execution emission (Abs.SupportedState allowed) view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := op::after}::rest,[]⟩ expected sourcePC pendingFlag)
    {raw : runtime.interp.Frame}
    {frameIndex : Usize}
    {pc : U32}
    (last : frameIndex.val+1=exec.frames.length)
    (lookup : exec.frames.val[frameIndex.val]?=some raw)
    (binding : FrameBinding store exec raw f)
    (slots : FrameSlots exec raw f)
    {compiled C targets next output}
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint emission (Store.decodeStore view code store) raw
      {f with code := op::after} compiled C targets next output)
    {front args consumed : List val}
    {returns : List valtype}
    {address : runtime.FuncAddr}
    {base : Usize}
    (split : f.vals=front++consumed)
    (destination : base.val=raw.base.val+Code.slots ((f.locals++front).map Code.valueType))
    (heights : ∀ label∈f.labels, label.height≤front.length)
    (continuation : Code.StructuredCodeWithTables (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Code.valueType++returns) after pc.val next output)
    (pending : Abs.HostPending
      ⟨Store.decodeStore view code store,ambient,{f with code := after,vals := front}::rest,[]⟩ returns)
    (memory : runtime.platform.MemoryBuffer M)
    (padded : runtime.interp.Execution)
    (function : runtime.store.FuncInst)
    (signature : Itasca.types.FuncType)
    (identity : Nat)
    (params : List valtype)
    (copied : alloc.vec.Vec runtime.Value)
    (host : HostFunction (Store.decodeStore view code store) address.index.val identity params
      (signature.results.val.map sourceType))
    (argumentsTyped : ResultsTyped (Store.decodeStore view code store) params args)
    (resultTypes : signature.results.val.map sourceType=returns)
    (frameWf : wf_frame f.toFrame)
    (functionAt : store.funcs.val[address.index.val]?=some function)
    (signatureAt : store.types.val[function.signature.val]?=some signature)
    (preparation : ∃padding,SlotsEffect {exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}} padded
      (exec.slots.val++padding))
    (frames : padded.frames=(exec.frames.set frameIndex {raw with pc:=pc}))
    (capacity : base.val+Code.slots (signature.results.val.map sourceType)≤padded.slots.length)
    (argumentsEq : copied.val.map sourceValue=args)
    (sourceOwned : Abs.Ownership.StateOwned (Store.ownershipBounds store)
      ⟨Store.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩)
    (sourcePending : Spec.OpenHost.Pending)
    (completion : ∀fresh returned,sourcePending.completed ⟨fresh,some returned⟩=
      Abs.decode ⟨fresh,ambient,{f with code:=after,vals:=front++returned}::rest,[]⟩) :
    SourceContinuation emission allowed memory view code store {padded with host_args:=copied}
      address base sourcePending expected := by
  refine ⟨function,signature,functionAt,signatureAt,?_⟩
  intro afterCode freshStore agrees retained externs bounds extension sourceTyped fresh values status issued
  apply WP.spec_mono (prepared_source_resume_at machine last lookup binding slots program point split destination heights continuation pending
    memory padded freshStore afterCode agrees function signature identity params copied values status host argumentsTyped resultTypes frameWf
    (retained.function_lookup functionAt) (retained.type_lookup signatureAt) issued preparation frames capacity argumentsEq retained bounds
    extension sourceTyped fresh sourcePending completion)
  intro out post successful
  obtain ⟨finalPC,resumed,owned,same⟩ := post.2 successful
  have beforeOwned : Abs.Ownership.StateOwned (Store.ownershipBounds store)
      ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ := by
    refine ⟨sourceOwned.1,?_⟩
    intro item member
    rcases List.mem_cons.mp member with rfl|member
    · exact sourceOwned.2 {item with code:=op::after} (List.mem_cons_self ..)
    · exact sourceOwned.2 item (List.mem_cons_of_mem _ member)
  have callerOwned : Abs.Ownership.StateOwned (Store.ownershipBounds freshStore)
      ⟨Store.decodeStore view afterCode freshStore,ambient,{f with code:=after,vals:=front++out.2.host_results.val.map sourceValue}::rest,[]⟩ :=
    beforeOwned.host_return (retained.ownership_extension externs) split owned
  exact ⟨_,finalPC,false,resumed,⟨callerOwned,fresh.shape.stateful_heap_owned afterCode⟩,same⟩
end Exec.Theorems.OpenReentrantControl
