import Exec.Theorems.Host.HostIndirectRecordedDispatch
import Exec.Theorems.Composition.Recorded.RecordedEventfulHistory
import Exec.Theorems.Host.HostEventfulReturn
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
open Exec.Interp.StructuredMachine
theorem step_indirect_host_recorded_success {M P F A : Type} {emission : FunctionEmission} {allowed : instr → Prop}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (Inv : runtime.store.Store M → Prop)
    (certify : ∀ s, Inv s → CertifiedSupportedStore emission allowed view code s)
    (sound : Platform.HostSound hooks Inv (Store.decodeStore view code))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv store)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [IndirectProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (table type : U32) (after : List instr)
    (position : Nat) (sourceOperands : List val) (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (host : U64)
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
    (preserve : ∀p args results answer,hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀p args results answer,hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀p args results answer,hooks.call_host p store host args results=.ok answer →
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value) :
    let before : EventfulMachine emission allowed M P view code expected :=
      ⟨store,exec,platform,⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩,
        raw.pc.val,false,machine,certify store valid,owned⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      Inv out.2.2.1 ∧ (out.1=.Ok () → ∃ events, ∃ final : EventfulMachine emission allowed M P view code expected,
        out=(.Ok (),final.exec,final.store,final.platform) ∧
        RecordedEventfulTransition memory hooks floats allocator before events final) ⦄ := by
  have certified := certify store valid
  dsimp only
  obtain ⟨⟨status,afterExec,afterStore,afterPlatform⟩,actual,outcome⟩ := WP.spec_imp_exists
    (step_indirect_host_structured_recording memory hooks floats allocator allocation interrupts view code Inv certify sound exec store platform valid
      frameIndex raw inst compiled C targets next output ambient f rest table type after position sourceOperands address function host
      positionSplit selectedSource functionAt hostCode owner last hf hi hc moduleEq binding slots program point expected machine owned.values preserve externs issued)
  rw [actual,WP.spec_ok]
  refine ⟨outcome.1, ?_⟩
  have outcome := outcome.2
  intro success
  change status=.Ok () at success
  subst status
  let before : EventfulMachine emission allowed M P view code expected :=
    ⟨store,exec,platform,⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩,
      raw.pc.val,false,machine,certify store valid,owned⟩
  rcases outcome with skip | called
  · obtain ⟨guard,fetch,_,sameStore,samePlatform,finalPC,resumed,simulation⟩ := skip
    change afterStore=store at sameStore
    change afterPlatform=platform at samePlatform
    subst afterStore
    subst afterPlatform
    let final : EventfulMachine emission allowed M P view code expected :=
      ⟨store,afterExec,platform,before.source,finalPC,false,resumed,certified,owned⟩
    exact ⟨[],final,rfl,⟨actual,(simulation.widen program.fetchBound).eventful,
      Spec.extend_store_refl _ machine.typed.typed.store,.refl store,rfl⟩,by simp only [stepHostEvents,guard]⟩
  · obtain ⟨guard,signature,base,pc,front,args,split,pcNext,fetch,callActual,fresh,retained,extension,external,causes,outcome⟩ := called
    rcases outcome with early | observed
    · obtain ⟨error,status,_,_,_⟩ := early
      cases status
    · obtain ⟨kind,⟨count,positive,trace⟩,resumption⟩ := observed
      obtain ⟨finalPC,resumed,returned⟩ := resumption rfl
      obtain ⟨final,execEq,storeEq,platformEq,sourceEq,edge⟩ := eventful_host_return memory hooks floats allocator before
        afterStore afterExec afterPlatform ambient {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after} rest front
        (args++[Abs.integerVal .I32 position]) (afterExec.host_results.val.map sourceValue) after finalPC rfl
        (by simpa only [List.append_assoc] using split) actual retained external extension fresh returned resumed
        (hostCallEvents address (.Ok (),afterExec,afterStore,afterPlatform)) count (by omega)
        (by simpa only [hostCallFrameResult] using trace)
      refine ⟨_,final,by simp only [execEq,storeEq,platformEq],edge,?_⟩
      simp only [stepHostEvents,guard,execEq,storeEq,platformEq]
end Exec.Theorems
