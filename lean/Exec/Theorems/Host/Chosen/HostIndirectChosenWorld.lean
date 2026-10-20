import Exec.Theorems.Host.Chosen.HostIndirectStructuredChosenWorld
import Exec.Theorems.Composition.World.ChosenWorldSourceStep
import Exec.Theorems.Host.Chosen.ChosenHostErrors
import Exec.Theorems.Host.HostEventfulReturn
import Exec.Theorems.Composition.Eventful.EventfulWorldStep
import Exec.Theorems.Composition.Eventful.EventfulWorldReinterpret
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
open Exec.Interp.StructuredMachine
theorem step_indirect_host_chosen_world_outcomes {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=Spec.firstVectorChoice) (occurrence : Nat) {M P F A : Type} {emission : FunctionEmission} {allowed : instr → Prop}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀ c s, Inv c s → CertifiedSupportedStore emission allowed view c s)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv code store)
    (entryTyped : Store_ok (Store.decodeStore view code store))
    (frameIndex : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    [IndirectProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (table type : U32) (after : List instr)
    (position : Nat) (sourceOperands : List val) (address : runtime.FuncAddr) (function : runtime.store.Function) (host : U64)
    (positionSplit : f.vals=sourceOperands++[Abs.integerVal .I32 position])
    (selectedSource : Abs.Indirect.resolve (Store.decodeStore view code store) f table.val type.val position=some address.index.val)
    (functionAt : store.funcs.val[address.index.val]?=some function) (hostCode : function.code=.Host host)
    (owner : address.store=store.id)
    (last : frameIndex.val+1=exec.frames.length) (hf : exec.frames.val[frameIndex.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst) (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module=Store.decodeInstance store inst)
    (binding : FrameBinding store exec raw f) (slots : FrameSlots exec raw f)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint emission (Store.decodeStore view code store) raw
      {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution emission (Abs.SupportedState allowed) view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩ expected raw.pc.val false)
    (owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store)
      ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩)
    (callback : ∀ p args results,
      hooks.call_host p store host args results ⦃ answer => ∃ afterCode,
        Store.CodeAgreesOn store code afterCode ∧ Inv afterCode answer.2.2.1 ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode answer.2.2.1) ∧
        Store_ok (Store.decodeStore view afterCode answer.2.2.1) ∧
        ∀ signature,store.types.val[function.signature.val]?=some signature →
          choices.host (occurrence+1) (Store.decodeStore view code store) address.index.val host.val
            (signature.params.val.map sourceType) (signature.results.val.map sourceType) (args.val.map sourceValue)=
            checkedHostReply memory view afterCode answer.2.2.1 signature ⟨answer.2.2.2⟩ answer.1 ⦄)
    (preserve : ∀p args results answer,hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀p args results answer,hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀p args results answer,hooks.call_host p store host args results=.ok answer →
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value) :
    runtime.interp.step memory hooks floats allocator exec store platform
      ⦃ out => ChosenWorldSourceStepResult choices occurrence (emission:=emission) (allowed:=allowed) (view:=view)
        memory hooks floats allocator Inv code expected exec store platform
        ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩ raw.pc.val false out ⦄ := by
  let before : EventfulMachine emission allowed M P view code expected :=
    ⟨store,exec,platform,
      ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩,
      raw.pc.val,false,machine,certify code store valid,owned⟩
  obtain ⟨⟨status,afterExec,afterStore,afterPlatform⟩,actual,outcome⟩ := WP.spec_imp_exists
    (step_indirect_host_structured_chosen_world admissible vector occurrence memory hooks floats allocator allocation interrupts view code Inv certify exec store platform valid entryTyped
      frameIndex raw inst compiled C targets next output ambient f rest table type after position sourceOperands address function host
      positionSplit selectedSource functionAt hostCode owner last hf hi hc moduleEq binding slots program point expected machine owned.values callback preserve externs issued)
  rw [actual,WP.spec_ok]
  rcases outcome with skip | called
  · obtain ⟨guard,fetch,success,sameStore,samePlatform,finalPC,resumed,simulation⟩ := skip
    change status=.Ok () at success
    subst status
    change afterStore=store at sameStore
    change afterPlatform=platform at samePlatform
    subst afterStore
    subst afterPlatform
    let final : EventfulMachine emission allowed M P view code expected :=
      ⟨store,afterExec,platform,before.source,finalPC,false,resumed,certify code store valid,owned⟩
    refine ⟨⟨code,final⟩,valid,rfl,?_,Spec.extend_store_refl _ machine.typed.typed.store,.refl store,rfl,?_⟩
    · simpa only [stepHostEvents,guard,before] using (ChosenConcreteSim.widen simulation program.fetchBound).eventful
    · intro index inst found function; rfl
  · obtain ⟨afterCode,agrees,freshInv,guard,signature,base,pc,front,args,split,pcNext,fetch,callActual,
        fresh,retained,extension,external,site,causes,effect⟩ := called
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
          {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after} rest front
          (args++[Abs.integerVal .I32 position]) (afterExec.host_results.val.map sourceValue) after finalPC
          (by simp only [EventfulMachine.change_code,before,same])
          (by simpa only [List.append_assoc] using split) actual retained external
          (by simpa only [EventfulMachine.change_code,before,same] using extension) fresh returned resumed
          (hostCallEvents address (.Ok (),afterExec,afterStore,afterPlatform)) count (by omega)
          (by simpa only [EventfulMachine.change_code,before,hostCallFrameResult] using (trace.erases admissible))
        have crossed := edge.world_reinterpret agrees
        refine ⟨⟨afterCode,final⟩,?_,?_,?_,?_,?_,?_,?_⟩
        · simpa only [storeEq] using freshInv
        · simp only [execEq,storeEq,platformEq]
        · exact Or.inr ⟨count,by omega,by simpa only [sourceEq,hostCallFrameResult,labels] using trace⟩
        · exact crossed.extension
        · exact crossed.metadata
        · exact crossed.ambient
        · exact crossed.agrees
    | Err error =>
      refine ⟨afterCode,freshInv,fresh,retained,agrees,extension,?_,Or.inr ?_⟩
      · rcases effect with early | observed
        · obtain ⟨failed,sameError,cause,sameStore,noEvents⟩ := early
          have equal : failed=error := by simpa only [core.result.Result.Err.injEq] using sameError.symm
          subst failed
          change afterStore=store at sameStore
          have sourceError := HostPreparationCause.chosen_eventful_error (choices:=choices) occurrence cause machine.typed.typed
          have noStepEvents : stepHostEvents exec store (.Err error,afterExec,afterStore,afterPlatform)=[] := labels.trans noEvents
          rw [noStepEvents,sameStore,same]
          exact sourceError
        · obtain ⟨kind,⟨count,positive,trace⟩,resumption⟩ := observed
          have sourceError := host_frame_chosen_eventful_error kind trace rfl
          simpa only [labels] using sourceError
      · exact ⟨rfl,frameIndex,raw,pc,address,signature,base,host,hf,pcNext,site,callActual,causes⟩
end Exec.Theorems
