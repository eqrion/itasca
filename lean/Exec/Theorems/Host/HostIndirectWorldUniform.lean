import Exec.Theorems.Host.HostIndirectStructuredWorld
import Exec.Theorems.Host.HostEventfulReturn
import Exec.Theorems.Composition.Uniform.UniformWorldHistory
import Exec.Theorems.Composition.Eventful.EventfulWorldReinterpret
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
open Exec.Interp.StructuredMachine
theorem step_indirect_host_world_uniform {M P F A : Type} {emission : FunctionEmission} {allowed : instr → Prop}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀ c s, Inv c s → CertifiedSupportedStore emission allowed view c s)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv code store)
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
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode answer.2.2.1) ⦄)
    (preserve : ∀p args results answer,hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀p args results answer,hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀p args results answer,hooks.call_host p store host args results=.ok answer →
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value) :
    let before : EventfulWorld emission allowed M P view expected :=
      ⟨code,⟨store,exec,platform,
        ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩,
        raw.pc.val,false,machine,certify code store valid,owned⟩⟩
    runtime.interp.step memory hooks floats allocator exec store platform
      ⦃ out => out.1=.Ok () → ∃ next : EventfulWorld emission allowed M P view expected,
        Inv next.code next.machine.store ∧ out=(.Ok (),next.machine.exec,next.machine.store,next.machine.platform) ∧
        UniformWorldTransition memory hooks floats allocator before (stepHostEvents exec store out) next ⦄ := by
  let before : EventfulMachine emission allowed M P view code expected :=
    ⟨store,exec,platform,
      ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩,
      raw.pc.val,false,machine,certify code store valid,owned⟩
  obtain ⟨⟨status,afterExec,afterStore,afterPlatform⟩,actual,outcome⟩ := WP.spec_imp_exists
    (step_indirect_host_structured_world memory hooks floats allocator allocation interrupts view code Inv certify exec store platform valid
      frameIndex raw inst compiled C targets next output ambient f rest table type after position sourceOperands address function host
      positionSplit selectedSource functionAt hostCode owner last hf hi hc moduleEq binding slots program point expected machine owned.values callback preserve externs issued)
  dsimp only
  rw [actual,WP.spec_ok]
  intro success
  change status=.Ok () at success
  subst status
  rcases outcome with skip | called
  · obtain ⟨guard,fetch,success,sameStore,samePlatform,finalPC,resumed,simulation⟩ := skip
    change afterStore=store at sameStore
    change afterPlatform=platform at samePlatform
    subst afterStore
    subst afterPlatform
    let final : EventfulMachine emission allowed M P view code expected :=
      ⟨store,afterExec,platform,before.source,finalPC,false,resumed,certify code store valid,owned⟩
    have edge : EventfulTransition memory hooks floats allocator before [] final :=
      ⟨actual,(simulation.widen program.fetchBound).eventful,
        Spec.extend_store_refl _ machine.typed.typed.store,.refl store,rfl⟩
    refine ⟨⟨code,final⟩,valid,rfl,?_⟩
    have pcBound : finalPC≤U32.max := by
      obtain ⟨current,_,_,_,_,_,_,samePC,_,_⟩ := resumed.cursor
      rw [←samePC]
      scalar_tac
    exact ⟨by simpa only [stepHostEvents,guard,before] using edge.world,
      by simpa only [stepHostEvents,guard,before,final] using simulation.uniform_same pcBound⟩
  · obtain ⟨afterCode,agrees,freshInv,guard,signature,base,pc,front,args,split,pcNext,fetch,callActual,
        fresh,retained,extension,external,site,causes,effect⟩ := called
    have same := Store.decodeStore_code_agrees view agrees
    have labels : stepHostEvents exec store (.Ok (),afterExec,afterStore,afterPlatform)=
        hostCallEvents address (.Ok (),afterExec,afterStore,afterPlatform) := by
      simp only [stepHostEvents,guard]
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
        (by simpa only [EventfulMachine.change_code,before,hostCallFrameResult] using trace)
      refine ⟨⟨afterCode,final⟩,?_,?_,?_⟩
      · simpa only [storeEq] using freshInv
      · simp only [execEq,storeEq,platformEq]
      · exact ⟨by simpa only [labels,before] using edge.world_reinterpret agrees,
        by simpa only [labels,before,EventfulMachine.change_code] using
          edge.simulation.uniform_of_events (by simp [hostCallEvents])⟩
end Exec.Theorems
