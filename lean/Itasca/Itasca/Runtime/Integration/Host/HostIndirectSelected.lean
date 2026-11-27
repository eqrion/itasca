import Itasca.Runtime.Interp.Recording
import Itasca.Runtime.SourceMachine.OwnershipExtension
import Itasca.Runtime.Integration.Execution.Ownership.Publication
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.Integration.Execution.History.State
import Itasca.Runtime.Integration.Host.HostCallContext
import Itasca.Runtime.SourceMachine.Indirect.HostSimulation
import Itasca.Runtime.Store.Invariant.HostSignature
import Itasca.Runtime.Spec.PrimitiveOperations
import Itasca.Runtime.Interp.HostCalls
import Itasca.Runtime.Interp.Machine.Calls.HostCallStack
import Itasca.Runtime.Integration.Execution.Ownership.ReferenceShape
import Itasca.Runtime.SourceMachine.TransitionAndHostPreparation
import Itasca.Runtime.Interp.Machine.CompiledFunctions
import Itasca.Runtime.SourceMachine.Indirect.HostTyping

open WebAssembly

open Itasca.Representation

/-! ## HostOwnership -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std Itasca.Interp

/-- The raw function prefix retains function addresses. External-reference
issuance is a separate namespace absent from the decoded specification store,
so its monotonicity remains explicit in this conditional transport lemma. -/
theorem _root_.Itasca.Store.MetadataExtended.ownership_extension {M : Type} {before after : runtime.store.Store M}
    (retained : Store.MetadataExtended before after)
    (externs : before.externs.length ≤ after.externs.length) :
    (Store.ownershipBounds before).Extends (Store.ownershipBounds after) := by
  refine ⟨?_,externs⟩
  have same := congrArg List.length retained.functions
  change (after.funcs.val.take before.funcs.val.length).length = before.funcs.val.length at same
  change before.funcs.val.length ≤ after.funcs.val.length
  rw [←same]
  simp only [List.length_take]
  exact Nat.min_le_right _ _

end Itasca.Interp
namespace Itasca.Integration
open Aeneas Aeneas.Std Itasca.Interp

/-- Checked returned values and fresh store shape restore all ownership facts
needed by the next interpreter iteration. The old caller's retained values
are transported through explicit raw namespace growth. -/
theorem host_return_stateful_owned {M : Type} {view : M → Slice U8} {code : Representation.CodeInterpretation}
    {before after : runtime.store.Store M} {ambient : frame} {caller : SourceMachine.AFrame}
    {rest : List SourceMachine.AFrame} {front args returned : List val} {continuation : List instr}
    (retained : Store.MetadataExtended before after)
    (externs : before.externs.length ≤ after.externs.length)
    (shape : Representation.Shape view after)
    (owned : SourceMachine.Ownership.StateOwned (Store.ownershipBounds before)
      ⟨Representation.decodeStore view code before,ambient,caller::rest,[]⟩)
    (split : caller.vals=front++args)
    (results : SourceMachine.Ownership.ValuesOwned (Store.ownershipBounds after) returned) :
    SourceMachine.Ownership.StatefulOwned (Store.ownershipBounds after)
      ⟨Representation.decodeStore view code after,ambient,{caller with code:=continuation,vals:=front++returned}::rest,[]⟩ :=
  ⟨owned.host_return (retained.ownership_extension externs) split results,shape.stateful_heap_owned code⟩
end Itasca.Integration

end

/-! ## HostEventfulReturn -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Interp

/-- A checked host result closes an actual eventful machine edge. The source
trace, runtime result check, fresh certificate and raw namespace preservation
are supplied by the host dispatch lemmas; no host behavior is postulated here. -/
theorem eventful_host_return {M P F A : Type}

    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Representation.CodeInterpretation} {expected : List valtype}
    (before : EventfulMachine M P view code expected)
    (afterStore : runtime.store.Store M) (afterExec : runtime.interp.Execution) (afterPlatform : P)
    (ambient : frame) (caller : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (front consumed returned : List val) (continuation : List instr) (pc : Nat)
    (source : before.source=⟨Representation.decodeStore view code before.store,ambient,caller::rest,[]⟩)
    (split : caller.vals=front++consumed)
    (actual : runtime.interp.step memory hooks floats allocator before.exec before.store before.platform=
      .ok (.Ok (),afterExec,afterStore,afterPlatform))
    (retained : Store.MetadataExtended before.store afterStore)
    (externs : before.store.externs.length≤afterStore.externs.length)
    (extension : Extend_store (Representation.decodeStore view code before.store) (Representation.decodeStore view code afterStore))
    (fresh : CertifiedSupportedStore view code afterStore)
    (checked : SourceMachine.Ownership.ValuesOwned (Store.ownershipBounds afterStore) returned)
    (resumed : Machine.Execution view code afterStore afterExec
      ⟨Representation.decodeStore view code afterStore,ambient,{caller with code:=continuation,vals:=front++returned}::rest,[]⟩ expected pc false)
    (events : List HostEvent) (count : Nat) (positive : 0<count)
    (trace : Spec.StepsHN count (SourceMachine.decode before.source) events
      (SourceMachine.decode ⟨Representation.decodeStore view code afterStore,ambient,
        {caller with code:=continuation,vals:=front++returned}::rest,[]⟩)) :
    ∃ after : EventfulMachine M P view code expected,
      after.exec=afterExec ∧ after.store=afterStore ∧ after.platform=afterPlatform ∧
      after.source=⟨Representation.decodeStore view code afterStore,ambient,
        {caller with code:=continuation,vals:=front++returned}::rest,[]⟩ ∧
      EventfulTransition memory hooks floats allocator before events after := by
  have oldOwned : SourceMachine.Ownership.StateOwned (Store.ownershipBounds before.store)
      ⟨Representation.decodeStore view code before.store,ambient,caller::rest,[]⟩ := by
    simpa only [source] using before.owned.values
  have owned := host_return_stateful_owned (continuation:=continuation) retained externs fresh.shape oldOwned split checked
  let after : EventfulMachine M P view code expected :=
    ⟨afterStore,afterExec,afterPlatform,_,pc,false,resumed,fresh,owned⟩
  refine ⟨after,rfl,rfl,rfl,rfl,actual,EventfulConcreteSim.of_steps positive trace,extension,retained,?_⟩
  change ambient=before.source.ambient
  rw [source]
end Itasca.Integration

end

/-! ## HostIndirectContext -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Interp

/-- The checked atomic host event composes with source call resolution and
all surrounding contexts. This retains a positive source step count. -/
theorem HostCallSourceOutcome.indirect_frame_events {M P : Type}
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (before : runtime.store.Store M) (ambient : frame) (f : SourceMachine.AFrame)
    (rest : List SourceMachine.AFrame) (after : List instr) (table type position : Nat)
    (address : runtime.FuncAddr) (front args : List val) (base : Usize)
    (exec : runtime.interp.Execution)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P)
    (observed : HostCallSourceOutcome view code before f.toFrame address args base exec out)
    (storeWf : wf_store (Representation.decodeStore view code before))
    (freshWf : wf_store (Representation.decodeStore view code out.2.2.1))
    (ambientWf : wf_frame ambient) (frameWf : wf_frame f.toFrame)
    (labels : SourceMachine.LabelsWf f.labels) (values : Forall wf_val front)
    (tail : Forall wf_instr after) (callers : Forall SourceMachine.FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (resolve : Spec.IndirectTarget (Representation.decodeStore view code before) f.toFrame table type position address.index.val)
    (tableBound : table < 2^32) (typeBound : type < 2^32) (positionBound : position < 2^32)
    (argsWf : Forall wf_val args) :
    ∃ n, 2 ≤ n ∧ Spec.StepsHN n
      (SourceMachine.decode ⟨Representation.decodeStore view code before,ambient,
        {f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type) :: after,vals := front ++ args ++ [SourceMachine.integerVal .I32 position]} :: rest,[]⟩)
      (hostCallEvents address out) (hostCallFrameResult view code ambient f rest after front out) := by
  obtain ⟨arguments,_,_,_,outcome⟩ := observed
  rcases outcome with ⟨success,_,source,_⟩ | ⟨failure,source,_⟩
  · refine ⟨2,by omega,?_⟩
    simpa only [hostCallEvents,hostCallFrameResult,success,arguments] using
      SourceMachine.Indirect.host_return_simulation _ _ ambient f rest after table type position address.index.val front args
        (out.2.1.host_results.val.map sourceValue) _ storeWf ambientWf frameWf labels values tail callers
        heights resolve tableBound typeBound positionBound argsWf source
  · obtain ⟨n,bound,trace⟩ := SourceMachine.Indirect.host_trap_simulation _ _ ambient f rest after table type position address.index.val
      front args _ storeWf freshWf ambientWf frameWf labels values tail callers heights resolve tableBound typeBound positionBound argsWf source
    refine ⟨n,bound,?_⟩
    rcases failure with trapped | exhausted
    · simpa only [hostCallEvents,hostCallFrameResult,trapped,arguments] using trace
    · simpa only [hostCallEvents,hostCallFrameResult,exhausted,arguments] using trace
end Itasca.Integration

end

/-! ## HostResumeOwned -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Interp

/-- Successful host checks produce exactly the encoded results; rejected
results and explicit host errors retain the callback's store in an atomic host
source transition. Stack exhaustion records that completed callback as a trap. -/
theorem host_resume_source_owned {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (before after : runtime.store.Store M) (ambient : frame)
    (exec : runtime.interp.Execution) (address : runtime.FuncAddr) (base : Usize)
    (function : runtime.store.FuncInst) (signature : Itasca.wasm_types.FuncType)
    (identity : Nat) (params : List valtype) (args : List val)
    (results : alloc.vec.Vec runtime.Value)
    (status : core.result.Result Unit runtime.platform.HostError)
    (host : HostFunction (Representation.decodeStore view code before) address.index.val identity
      params (signature.results.val.map Itasca.Translation.valueType))
    (arguments : ResultsTyped (Representation.decodeStore view code before) params args)
    (extension : Extend_store (Representation.decodeStore view code before) (Representation.decodeStore view code after))
    (sourceTyped : Store_ok (Representation.decodeStore view code after))
    (wfAmbient : wf_frame ambient)
    (functionAt : after.funcs.val[address.index.val]? = some function)
    (signatureAt : after.types.val[function.signature.val]? = some signature)
    (issued : ∀ value ∈ results.val, Store.IssuedValue after value)
    (capacity : base.val + Representation.slots (signature.results.val.map Itasca.Translation.valueType) ≤ exec.slots.length) :
    hostResume memory exec after address base results status ⦃ out =>
      out.2.host_args = exec.host_args ∧ out.2.host_results = results ∧
      out.2.frames = exec.frames ∧ out.2.store = exec.store ∧
      ((out.1 = .Ok () ∧
        StepH ⟨⟨Representation.decodeStore view code before,ambient⟩,vals args ++ [.CALL_ADDR address.index.val]⟩
          [.call address.index.val args (some (results.val.map sourceValue))]
          ⟨⟨Representation.decodeStore view code after,ambient⟩,vals (results.val.map sourceValue)⟩ ∧
        ResultsTyped (Representation.decodeStore view code after) (signature.results.val.map Itasca.Translation.valueType)
          (results.val.map sourceValue) ∧
        SourceMachine.Ownership.ValuesOwned (Store.ownershipBounds after) (results.val.map sourceValue) ∧
        ValuesAt out.2.slots.val base.val (results.val.map sourceValue) ∧
        out.2.slots.length = exec.slots.length ∧
        (∀ j, j < base.val ∨ base.val + Representation.slots (signature.results.val.map Itasca.Translation.valueType) ≤ j →
          out.2.slots.val[j]? = exec.slots.val[j]?)) ∨
       ((out.1 = .Err (.Trap .Host) ∨ out.1 = .Err (.Exhausted .CallStack) ∧ status = .Err .StackOverflow) ∧
        out.2.slots = exec.slots ∧
        StepH ⟨⟨Representation.decodeStore view code before,ambient⟩,vals args ++ [.CALL_ADDR address.index.val]⟩
          [.call address.index.val args none] ⟨⟨Representation.decodeStore view code after,ambient⟩,[.TRAP]⟩)) ⦄ := by
  cases status with
  | Err error =>
    cases error <;> simp only [hostResume,WP.spec_ok]
    · exact ⟨by trivial,by trivial,by trivial,by trivial,Or.inr ⟨Or.inl (by trivial),by trivial,Spec.host_trap_step host arguments extension sourceTyped wfAmbient⟩⟩
    · exact ⟨by trivial,by trivial,by trivial,by trivial,Or.inr ⟨Or.inr ⟨by trivial,by trivial⟩,by trivial,Spec.host_trap_step host arguments extension sourceTyped wfAmbient⟩⟩
  | Ok unitValue =>
    cases unitValue
    unfold hostResume
    step with vec_index_given after.funcs address.index function functionAt as ⟨found,same⟩
    subst found
    step with vec_index_given after.types function.signature signature signatureAt as ⟨found,same⟩
    subst found
    step with Store.check_values_source_typed memory view code after (Spec.extend_store_wf extension).2
      results.slice signature.results.slice issued as ⟨checked,accepted⟩
    cases checked with
    | Err error =>
      simp only [check_failed_eq,bind_ok,ite_true,WP.spec_ok]
      exact ⟨by trivial,by trivial,by trivial,by trivial,Or.inr ⟨Or.inl (by trivial),by trivial,Spec.host_trap_step host arguments extension sourceTyped wfAmbient⟩⟩
    | Ok unitValue =>
      cases unitValue
      obtain ⟨typed,owned,tags⟩ := accepted rfl
      simp only [check_failed_eq,bind_ok,Bool.false_eq_true,ite_false]
      have widths : (Representation.encodeValues (results.val.map sourceValue)).length =
          Representation.slots (signature.results.val.map Itasca.Translation.valueType) := by
        rw [Representation.encode_values_length]
        simp only [List.map_map,Function.comp_def,source_value_type]
        change signature.results.val = results.val.map rawType at tags
        rw [tags,List.map_map]
        rfl
      step with host_results_encode exec.slots results signature.results after.id base tags
        (fun value member => (owned value member).1) (by rw [widths]; exact capacity)
        as ⟨words,length,represented,preserved⟩
      exact Or.inl ⟨Spec.host_return_step host arguments extension sourceTyped typed wfAmbient,
        typed,Store.source_values_owned after results.val owned,represented,length,by simpa only [widths] using preserved⟩
end Itasca.Integration

end

/-! ## HostCallFrames -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Interp

/-- Successful actual host calls supply the concrete slot/frame transport used
when resuming a caller; no callback behavior is hidden in that transport. -/
theorem HostCallSourceOutcome.return_effect {M P : Type}
    {view : M → Slice U8} {code : Representation.CodeInterpretation} {before : runtime.store.Store M}
    {ambient : frame} {address : runtime.FuncAddr} {args : List val} {base : Usize}
    {exec : runtime.interp.Execution}
    {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}
    (observed : HostCallSourceOutcome view code before ambient address args base exec out)
    (success : out.1 = .Ok ()) :
    HostReturnEffect exec out.2.1 base.val (out.2.1.host_results.val.map sourceValue) := by
  obtain ⟨arguments,frames,identity,capacity,outcome⟩ := observed
  rcases outcome with returned | failed
  · obtain ⟨_,values,source,preserved⟩ := returned
    exact ⟨identity,frames,capacity,values,fun j bound below => preserved j bound (Or.inl below)⟩
  · rcases failed.1 with status | status <;> rw [success] at status <;> cases status

end Itasca.Integration

end

/-! ## HostStructuredResume -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Interp
open Itasca.Interp.Machine

theorem structured_host_next (s : WebAssembly.store) (ambient : frame) (f : SourceMachine.AFrame)
    (rest : List SourceMachine.AFrame) (after : List instr) (index address identity : Nat)
    (params results : List valtype) (front args : List val)
    (resolve : f.module.FUNCS[index]? = some address)
    (host : HostFunction s address identity params results)
    (argumentTypes : args.map Representation.valueType = params) :
    SourceMachine.astep ⟨s,ambient,{f with code := .CALL (.mk_uN index)::after,vals := front++args}::rest,[]⟩ =
      .host address args results ⟨s,ambient,{f with code := after,vals := front}::rest,[]⟩ := by
  obtain ⟨moduleInst,lookup⟩ := host
  have types : args.map SourceMachine.valueType = params := by
    have same : SourceMachine.valueType = Representation.valueType := by funext v; exact (value_type_eq_abs v).symm
    rw [same,argumentTypes]
  have length : params.length = args.length := by rw [← argumentTypes,List.length_map]
  simp [SourceMachine.astep,SourceMachine.call,resolve,lookup,length,types]

/-- Checked host results resume the complete generic machine. Raw metadata
retention is explicit; newly added functions come from the fresh certificate. -/
theorem host_structured_resume {M P : Type}
    {view : M → Slice U8} {code : Representation.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {ambient : frame} {f : SourceMachine.AFrame} {rest : List SourceMachine.AFrame} {op : instr} {after : List instr}
    {expected : List valtype} {sourcePC : Nat} {pendingFlag : Bool}
    (machine : Execution view code store exec
      ⟨Representation.decodeStore view code store,ambient,{f with code := op::after}::rest,[]⟩ expected sourcePC pendingFlag)
    {raw : runtime.interp.Frame} {frameIndex : Usize} {pc : U32}
    (last : frameIndex.val+1=exec.frames.length)
    (lookup : exec.frames.val[frameIndex.val]?=some raw)
    (binding : FrameBinding store exec raw f) (slots : FrameSlots exec raw f)
    {compiled C targets next output}
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Representation.decodeStore view code store) raw
      {f with code := op::after} compiled C targets next output)
    {front args consumed : List val} {returns : List valtype} {address : runtime.FuncAddr} {base : Usize}
    (split : f.vals=front++consumed)
    (destination : base.val=raw.base.val+Representation.slots ((f.locals++front).map Representation.valueType))
    (heights : ∀ label∈f.labels, label.height≤front.length)
    (continuation : Compiler.StructuredCode (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Representation.valueType++returns) after pc.val next output)
    (pending : SourceMachine.HostPending
      ⟨Representation.decodeStore view code store,ambient,{f with code := after,vals := front}::rest,[]⟩ returns)
    {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}
    {callFrame : frame}
    (observed : HostCallSourceOutcome view code store callFrame address args base
      {exec with frames := exec.frames.set frameIndex {raw with pc := pc}} out)
    (success : out.1=.Ok ())
    (retained : Store.MetadataExtended store out.2.2.1) (bounds : FrameTypeBounds store)
    (extension : Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view code out.2.2.1))
    (fresh : CertifiedSupportedStore view code out.2.2.1)
    (returned : ResultsTyped (Representation.decodeStore view code out.2.2.1) returns (out.2.1.host_results.val.map sourceValue)) :
    ∃ finalPC, Execution view code out.2.2.1 out.2.1
      ⟨Representation.decodeStore view code out.2.2.1,ambient,
        {f with code := after,vals := front++out.2.1.host_results.val.map sourceValue}::rest,[]⟩ expected finalPC false := by
  have valueTypes : (out.2.1.host_results.val.map sourceValue).map Representation.valueType=returns := by
    have same : Representation.valueType = SourceMachine.valueType := by funext v; exact value_type_eq_abs v
    rw [same]; exact SourceMachine.results_type_of_typed returned
  obtain ⟨stack,ready⟩ := machine.stack.host_call_return raw frameIndex pc last lookup binding slots program point
    front consumed after returns base.val split destination heights continuation out.2.2.1
    (Representation.decodeStore view code out.2.2.1) retained bounds extension out.2.1
    (out.2.1.host_results.val.map sourceValue) (observed.return_effect success) valueTypes
  obtain ⟨finalPC,cursor⟩ := ready.cursor
  refine ⟨finalPC,rfl,⟨?_,fresh.contents_typed⟩,?_,?_,stack,cursor⟩
  · exact pending.finish_typed extension fresh.functions_typed returned
  · refine ⟨?_,fresh.supported⟩
    intro item member
    rcases List.mem_cons.mp member with rfl | member
    · have old := machine.core.active _ (List.mem_cons_self ..)
      exact ⟨fun instruction member => old.1 instruction (List.mem_cons_of_mem _ member),old.2⟩
    · exact machine.core.active item (List.mem_cons_of_mem _ member)
  · exact SourceMachine.FramesReturn.replace machine.result rfl
end Itasca.Integration

end

/-! ## HostIndirectSelected -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Interp
open Itasca.Interp.Machine

theorem structured_indirect_host_next (s : WebAssembly.store) (ambient : frame) (f : SourceMachine.AFrame)
    (rest : List SourceMachine.AFrame) (after : List instr) (table type position address identity : Nat)
    (params results : List valtype) (front args : List val)
    (resolved : SourceMachine.Indirect.resolve s f table type position=some address)
    (bounded : position<2^32) (host : HostFunction s address identity params results)
    (argumentTypes : args.map Representation.valueType=params) :
    SourceMachine.Indirect.step ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after, vals:=(front++args)++[SourceMachine.integerVal .I32 position]}::rest,[]⟩
      {f with vals:=(front++args)++[SourceMachine.integerVal .I32 position]} rest table type after =
      .host address args results ⟨s,ambient,{f with code:=after,vals:=front}::rest,[]⟩ := by
  obtain ⟨moduleInst,lookup⟩ := host
  have types : args.map SourceMachine.valueType=params := by
    simpa only [show Representation.valueType=SourceMachine.valueType from funext value_type_eq_abs] using argumentTypes
  have length : params.length=args.length := by rw [←argumentTypes,List.length_map]
  have decoded : SourceMachine.integer numtype.I32 (SourceMachine.integerVal .I32 position)=some position := SourceMachine.integer_accepts .I32 position bounded
  have resolved' : SourceMachine.Indirect.resolve s {f with vals:=(front++args)++[SourceMachine.integerVal .I32 position]} table type position=some address := resolved
  simp only [SourceMachine.Indirect.step,SourceMachine.pop_append,decoded,resolved']
  simp [SourceMachine.Indirect.invoke,lookup,length,types]

end Itasca.Integration

end

/-! Callback replies and source host events agree after dynamic result checks. -/
namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Interp Itasca.Platform Itasca.Representation

/-- The event reflects the actual raw reply and the public signature/ownership
check. An ordinary callback success with invalid results is a source host trap. -/
theorem host_resume_matches_observation {M P : Type}
    (memory : runtime.platform.MemoryBuffer M) (observed : HostObservation M)
    (exec : runtime.interp.Execution) (address : runtime.FuncAddr) (base : Usize) (platform : P)
    (metadata : ∃ beforeFunction afterFunction signature,
      observed.before.funcs.val[address.index.val]? = some beforeFunction ∧
      beforeFunction.code = .Host observed.identity ∧
      observed.after.funcs.val[address.index.val]? = some afterFunction ∧
      observed.after.types.val[afterFunction.signature.val]? = some signature)
    (arguments : exec.host_args.val = observed.arguments.val)
    (result : core.result.Result Unit runtime.ExecError) (finished : runtime.interp.Execution)
    (run : hostResume memory exec observed.after address base ⟨observed.returned⟩ observed.result =
      .ok (result, finished)) :
    List.Forall₂ HostObservation.Matches [observed]
      (hostCallEvents address (result, finished, observed.after, platform)) := by
  obtain ⟨beforeFunction,afterFunction,signature,beforeAt,host,afterAt,signatureAt⟩ := metadata
  have accepted_iff : observed.Accepted address.index.val ↔
      List.Forall₂ (ArgumentMatches observed.after.id) observed.returned.val signature.results.val := by
    constructor
    · rintro ⟨function, ty, found, typed, values⟩
      have same : function = afterFunction := Option.some.inj (found.symm.trans afterAt)
      subst function
      have same : ty = signature := Option.some.inj (typed.symm.trans signatureAt)
      subst ty
      exact values
    · intro values
      exact ⟨afterFunction, signature, afterAt, signatureAt, values⟩
  cases status : observed.result with
  | Err error =>
    cases error <;> simp only [hostResume, status, Result.ok.injEq, Prod.mk.injEq] at run
    all_goals rcases run with ⟨rfl, rfl⟩
    all_goals simp only [hostCallEvents, List.forall₂_cons, List.Forall₂.nil, and_true,
      HostObservation.Matches, status]
    all_goals exact ⟨⟨beforeFunction, beforeAt, host⟩, by simp only [arguments, ne_eq, reduceCtorEq, not_false_eq_true, true_or, and_true]⟩
  | Ok unitValue =>
    cases unitValue
    obtain ⟨checked, checkedEq, typed⟩ := WP.spec_imp_exists
      (check_values_accepts_iff memory observed.after observed.returned signature.results.slice)
    change checked = .Ok () ↔ List.Forall₂ (ArgumentMatches observed.after.id) observed.returned.val signature.results.val at typed
    simp only [hostResume, status, vec_index_eq _ _ _ afterAt,
      vec_index_eq _ _ _ signatureAt, bind_ok, checkedEq] at run
    cases checked with
    | Err error =>
      simp only [check_failed_eq, bind_ok, ite_true, Result.ok.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl⟩
      have rejected : ¬observed.Accepted address.index.val := by
        intro accepted
        have impossible := typed.mpr (accepted_iff.mp accepted)
        cases impossible
      simp only [hostCallEvents, List.forall₂_cons, List.Forall₂.nil, and_true, HostObservation.Matches]
      exact ⟨⟨beforeFunction, beforeAt, host⟩, by simp only [arguments], Or.inr rejected⟩
    | Ok unitValue =>
      cases unitValue
      simp only [check_failed_eq, bind_ok, Bool.false_eq_true, ite_false] at run
      obtain ⟨words, _copied, returned⟩ := Computation.bind_ok_inv _ _ _ run
      simp only [Result.ok.injEq, Prod.mk.injEq] at returned
      rcases returned with ⟨rfl, rfl⟩
      simp only [hostCallEvents, List.forall₂_cons, List.Forall₂.nil, and_true, HostObservation.Matches]
      exact ⟨⟨beforeFunction, beforeAt, host⟩, by simp only [arguments],
        status, accepted_iff.mpr (typed.mp rfl), rfl⟩

end Itasca.Integration
