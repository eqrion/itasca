import Exec.Theorems.Host.HostDirectEventful
import Exec.Interp.Host.HostRecording
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
open Exec.Interp.StructuredMachine

/-- At a fetched direct host site the instrumented instruction and the actual
selected call append the same observed event. Source labels are tied to that
callsite equation, independently of any existential history labels. -/
theorem step_host_call_recorded_eventful_success {M P F A : Type} {emission : FunctionEmission} {allowed : instr → Prop}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (sound : Platform.HostSound hooks (CertifiedSupportedStore emission allowed view code) (Store.decodeStore view code))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedSupportedStore emission allowed view code store)
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
    (prior : List HostEvent)
    (issued : ∀ p args results answer,
      hooks.call_host p store host args results=.ok answer →
      ∀ value∈answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value) :
    let before : EventfulMachine emission allowed M P view code expected :=
      ⟨store,exec,platform,⟨Store.decodeStore view code store,ambient,{f with code:=.CALL (.mk_uN index.val)::after}::rest,[]⟩,
        raw.pc.val,false,machine,certified,owned⟩
    Platform.Recording.run (runtime.interp.step memory hooks floats allocator exec store platform)
      (hostCallEvents address) prior ⦃ (out,trace) =>
        trace = prior ++ hostCallEvents address out ∧
        (∃ base pc, pc.val = raw.pc.val+1 ∧
          ∀ previous, recordedHostCall memory hooks floats allocator
            {exec with frames := exec.frames.set frameIndex {raw with pc := pc}}
            store platform address base previous = .ok (out,previous ++ hostCallEvents address out)) ∧
        (out.1=.Ok () → ∃ final : EventfulMachine emission allowed M P view code expected,
          out=(.Ok (),final.exec,final.store,final.platform) ∧
          EventfulTransition memory hooks floats allocator before (hostCallEvents address out) final) ⦄ := by
  dsimp only
  obtain ⟨out,actual,fresh,kept,extension,externCount,signature,base,pc,front,args,split,nextPC,callActual,causes,effect⟩ :=
    WP.spec_imp_exists (step_host_call_structured_provenance memory hooks floats allocator allocation interrupts view code
      sound exec store platform certified frameIndex raw caller compiled C targets next output ambient f rest index offset after
      address function host expected last hf hi hc fetched addressAt functionAt hostCode binding slots program point machine
      owned.values preserve externs issued)
  have eventful := step_host_call_eventful_success memory hooks floats allocator allocation interrupts view code
    sound exec store platform certified frameIndex raw caller compiled C targets next output ambient f rest index offset after
    address function host expected last hf hi hc fetched addressAt functionAt hostCode binding slots program point machine
    owned preserve externs issued
  dsimp only at eventful
  rw [actual,WP.spec_ok] at eventful
  simp only [Platform.Recording.run,actual,bind_ok,WP.spec_ok]
  refine ⟨rfl,⟨base,pc,nextPC,?_⟩,eventful⟩
  intro previous
  exact (Platform.Recording.returned _ (hostCallEvents address) previous out _).mpr ⟨callActual,rfl⟩
end Exec.Theorems
