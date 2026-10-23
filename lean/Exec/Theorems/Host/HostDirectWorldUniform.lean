import Exec.Theorems.Host.HostCallStructuredWorld
import Exec.Theorems.Host.HostEventfulReturn
import Exec.Theorems.Composition.Uniform.UniformWorldHistory
import Exec.Theorems.Composition.Eventful.EventfulWorldReinterpret
import Exec.Interp.Relations.StepRecordingLookup
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
open Exec.Interp.StructuredMachine
theorem step_host_call_world_uniform {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀ c s, Inv c s → CertifiedSupportedStore view c s)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv code store)
    (frameIndex : Usize) (raw : runtime.interp.Frame)
    (caller : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (index offset : U32) (after : List instr)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (host : U64)
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
    (point : FramePoint (Store.decodeStore view code store) raw
      {f with code := .CALL (.mk_uN index.val)::after} compiled C targets next output)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩ expected raw.pc.val false)
    (owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store)
      ⟨Store.decodeStore view code store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩)
    (callback : ∀ p args results,
      hooks.call_host p store host args results ⦃ answer => ∃ afterCode,
        Store.CodeAgreesOn store code afterCode ∧ Inv afterCode answer.2.2.1 ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode answer.2.2.1) ∧
        Store_ok (Store.decodeStore view afterCode answer.2.2.1) ⦄)
    (preserve : ∀ p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀ p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀ p args results answer,
      hooks.call_host p store host args results=.ok answer →
      ∀ value∈answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value) :
    let before : EventfulWorld M P view expected :=
      ⟨code,⟨store,exec,platform,
        ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL (.mk_uN index.val)::after}::rest,[]⟩,
        raw.pc.val,false,machine,certify code store valid,owned⟩⟩
    runtime.interp.step memory hooks floats allocator exec store platform
      ⦃ out => out.1=.Ok () → ∃ next : EventfulWorld M P view expected,
        Inv next.code next.machine.store ∧ out=(.Ok (),next.machine.exec,next.machine.store,next.machine.platform) ∧
        UniformWorldTransition memory hooks floats allocator before (stepHostEvents exec store out) next ⦄ := by
  let before : EventfulMachine M P view code expected :=
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
  intro success
  change status=.Ok () at success
  subst status
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
      {f with code:=.CALL (.mk_uN index.val)::after} rest front args
      (afterExec.host_results.val.map sourceValue) after finalPC
      (by simp only [EventfulMachine.change_code,before,same]) split actual retained external
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
