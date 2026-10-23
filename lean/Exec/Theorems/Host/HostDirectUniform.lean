import Exec.Theorems.Host.HostCallStructuredInvariant
import Exec.Theorems.Host.HostEventfulReturn
import Exec.Theorems.Composition.Uniform.UniformEventfulHistory
import Exec.Interp.Machines.Uniform.UniformSourceControl
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
open Exec.Interp.StructuredMachine
theorem step_host_call_uniform_invariant_success {M P F A : Type} {emission : FunctionEmission} {allowed : instr → Prop}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (Inv : runtime.store.Store M → Prop)
    (certify : ∀ s, Inv s → CertifiedSupportedStore emission allowed view code s)
    (sound : Platform.HostSound hooks Inv (Store.decodeStore view code))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv store)
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
    (point : FramePoint emission (Store.decodeStore view code store) raw
      {f with code := .CALL (.mk_uN index.val)::after} compiled C targets next output)
    (machine : Execution emission (Abs.SupportedState allowed) view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩ expected raw.pc.val false)
    (owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store)
      ⟨Store.decodeStore view code store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩)
    (preserve : ∀ p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀ p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀ p args results answer,
      hooks.call_host p store host args results=.ok answer →
      ∀ value∈answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value) :
    let before : EventfulMachine emission allowed M P view code expected :=
      ⟨store,exec,platform,⟨Store.decodeStore view code store,ambient,{f with code:=.CALL (.mk_uN index.val)::after}::rest,[]⟩,
        raw.pc.val,false,machine,certify store valid,owned⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      Inv out.2.2.1 ∧ (out.1=.Ok () → ∃ final : EventfulMachine emission allowed M P view code expected,
        out=(.Ok (),final.exec,final.store,final.platform) ∧
        UniformEventfulTransition memory hooks floats allocator before (hostCallEvents address out) final) ⦄ := by
  have certified := certify store valid
  dsimp only
  obtain ⟨⟨status,afterExec,afterStore,afterPlatform⟩,actual,outcome⟩ := WP.spec_imp_exists
    (step_host_call_structured_invariant_provenance memory hooks floats allocator allocation interrupts view code Inv certify sound exec store platform valid
      frameIndex raw caller compiled C targets next output ambient f rest index offset after address function host expected
      last hf hi hc fetched addressAt functionAt hostCode binding slots program point machine owned.values preserve externs issued)
  rw [actual,WP.spec_ok]
  refine ⟨outcome.1, ?_⟩
  have outcome := outcome.2
  intro success
  change status=.Ok () at success
  subst status
  obtain ⟨fresh,retained,extension,external,signature,base,pc,front,args,split,pcNext,callActual,causes,outcome⟩ := outcome
  rcases outcome with early | observed
  · obtain ⟨error,status,_,_,_⟩ := early
    cases status
  · obtain ⟨kind,⟨count,positive,trace⟩,resumption⟩ := observed
    obtain ⟨finalPC,resumed,returned⟩ := resumption rfl
    let before : EventfulMachine emission allowed M P view code expected :=
      ⟨store,exec,platform,⟨Store.decodeStore view code store,ambient,{f with code:=.CALL (.mk_uN index.val)::after}::rest,[]⟩,
        raw.pc.val,false,machine,certify store valid,owned⟩
    obtain ⟨final,execEq,storeEq,platformEq,sourceEq,edge⟩ := eventful_host_return memory hooks floats allocator before
      afterStore afterExec afterPlatform ambient {f with code:=.CALL (.mk_uN index.val)::after} rest front args
      (afterExec.host_results.val.map sourceValue) after finalPC rfl split actual retained external extension fresh returned resumed
      (hostCallEvents address (.Ok (),afterExec,afterStore,afterPlatform)) count (by omega)
      (by simpa only [hostCallFrameResult] using trace)
    exact ⟨final,by simp only [execEq,storeEq,platformEq],edge,
      edge.simulation.uniform_of_events (by simp [hostCallEvents])⟩
end Exec.Theorems
