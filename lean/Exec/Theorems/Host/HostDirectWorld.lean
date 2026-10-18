import Exec.Theorems.Host.HostCallStructuredWorld
import Exec.Theorems.Host.HostEventfulReturn
import Exec.Theorems.Composition.Eventful.EventfulWorldStep
import Exec.Theorems.Composition.Eventful.EventfulWorldReinterpret
import Exec.Interp.Relations.StepRecordingLookup
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
open Exec.Interp.StructuredMachine
theorem step_host_call_world_outcomes {M P F A : Type} {emission : FunctionEmission} {allowed : instr → Prop}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀ c s, Inv c s → CertifiedSupportedStore emission allowed view c s)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv code store)
    (frameIndex : Usize) (raw : runtime.interp.Frame)
    (caller : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (index offset : U32) (after : List instr)
    (address : runtime.FuncAddr) (function : runtime.store.Function) (host : U64)
    (expected : List valtype)
    (last : frameIndex.val+1=exec.frames.length)
    (hf : exec.frames.val[frameIndex.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some caller)
    (hc : caller.module.functions.val[raw.function.val]?=some compiled)
    (fetched : compiled.code.val[raw.pc.val]?=some (.Call index offset))
    (addressAt : caller.funcs.val[index.val]?=some address)
    (functionAt : store.funcs.val[address.index.val]?=some function)
    (hostCode : function.code=.Host host)
    (binding : FrameBinding store exec raw f) (slots : FrameSlots exec raw f)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint emission (Store.decodeStore view code store) raw
      {f with code := .CALL (.mk_uN index.val)::after} compiled C targets next output)
    (machine : Execution emission (Abs.SupportedState allowed) view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩ expected raw.pc.val false)
    (owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store)
      ⟨Store.decodeStore view code store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩)
    (callback : ∀ p args results,
      hooks.call_host p store host args results ⦃ answer => ∃ afterCode,
        Store.CodeAgreesOn store code afterCode ∧ Inv afterCode answer.2.2.1 ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode answer.2.2.1) ⦄)
    (preserve : ∀ p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀ p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀ p args results answer,
      hooks.call_host p store host args results=.ok answer →
      ∀ value∈answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value) :
    let before : EventfulWorld emission allowed M P view expected :=
      ⟨code,⟨store,exec,platform,
        ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL (.mk_uN index.val)::after}::rest,[]⟩,
        raw.pc.val,false,machine,certify code store valid,owned⟩⟩
    runtime.interp.step memory hooks floats allocator exec store platform
      ⦃ out => WorldStepResult memory hooks floats allocator Inv before out ⦄ := by
  let before : EventfulMachine emission allowed M P view code expected :=
    ⟨store,exec,platform,
      ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL (.mk_uN index.val)::after}::rest,[]⟩,
      raw.pc.val,false,machine,certify code store valid,owned⟩
  have guard : hostStepAddress exec store=some address := by
    rw [hostStepAddress_at exec store frameIndex raw caller compiled (.Call index offset) last hf hi hc fetched]
    exact hostInstructionAddress_direct exec store raw caller compiled index offset address function host addressAt functionAt hostCode
  obtain ⟨⟨status,afterExec,afterStore,afterPlatform⟩,actual,afterCode,agrees,freshInv,fresh,
      retained,extension,external,signature,base,pc,front,args,split,pcNext,site,callActual,causes,effect⟩ :=
    WP.spec_imp_exists (step_host_call_structured_world_provenance memory hooks floats allocator allocation interrupts
      view code Inv certify exec store platform valid frameIndex raw caller compiled C targets next output ambient f rest
      index offset after address function host expected last hf hi hc fetched addressAt functionAt hostCode binding slots
      program point machine owned.values callback preserve externs issued)
  dsimp only
  rw [actual,WP.spec_ok]
  have same := Store.decodeStore_code_agrees view agrees
  have labels : stepHostEvents exec store (status,afterExec,afterStore,afterPlatform)=
      hostCallEvents address (status,afterExec,afterStore,afterPlatform) := by
    simp only [stepHostEvents,guard]
  cases status with
  | Ok unit =>
    cases unit
    rcases effect with early | observed
    · obtain ⟨error,failed,_⟩ := early
      cases failed
    · obtain ⟨kind,⟨count,positive,trace⟩,resumption⟩ := observed
      obtain ⟨finalPC,resumed,returned⟩ := resumption rfl
      obtain ⟨final,execEq,storeEq,platformEq,sourceEq,edge⟩ := eventful_host_return memory hooks floats allocator
        (before.change_code afterCode agrees) afterStore afterExec afterPlatform ambient
        {f with code:=.CALL (.mk_uN index.val)::after} rest front args
        (afterExec.host_results.val.map sourceValue) after finalPC
        (by simp only [EventfulMachine.change_code,before,same]) split actual retained external
        (by simpa only [EventfulMachine.change_code,before,same] using extension) fresh returned resumed
        (hostCallEvents address (.Ok (),afterExec,afterStore,afterPlatform)) count (by omega)
        (by simpa only [EventfulMachine.change_code,before,hostCallFrameResult] using trace)
      refine ⟨⟨afterCode,final⟩,?_,?_,?_⟩
      · simpa only [storeEq] using freshInv
      · simp only [execEq,storeEq,platformEq]
      · simpa only [labels,before] using edge.world_reinterpret agrees
  | Err error =>
    refine ⟨afterCode,freshInv,fresh,retained,agrees,extension,?_,Or.inr ?_⟩
    · rcases effect with early | observed
      · obtain ⟨failed,sameError,cause,sameStore,noEvents⟩ := early
        have equal : failed=error := by simpa only [core.result.Result.Err.injEq] using sameError.symm
        subst failed
        change afterStore=store at sameStore
        have sourceError := HostPreparationCause.eventful_error cause machine.typed.typed
        have noStepEvents : stepHostEvents exec store (.Err error,afterExec,afterStore,afterPlatform)=[] := labels.trans noEvents
        rw [noStepEvents,sameStore,same]
        exact sourceError
      · obtain ⟨kind,⟨count,positive,trace⟩,resumption⟩ := observed
        have sourceError := host_frame_eventful_error kind trace.erase rfl
        simpa only [labels] using sourceError
    · exact ⟨rfl,frameIndex,raw,pc,address,signature,base,host,hf,pcNext,site,callActual,causes⟩
end Exec.Theorems
