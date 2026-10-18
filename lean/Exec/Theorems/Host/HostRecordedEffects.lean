import Exec.Theorems.Host.HostCallStructuredInvariant
import Exec.Theorems.Host.HostIndirectRecordedDispatch
import Exec.Theorems.Composition.Eventful.EventfulErrors
import Exec.Interp.Relations.StepRecordingLookup
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
open Exec.Interp.StructuredMachine
theorem step_host_call_recorded_effects {M P F A : Type} {emission : FunctionEmission} {allowed : instr → Prop}
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
    (owned : Abs.Ownership.StateOwned (Store.ownershipBounds store)
      ⟨Store.decodeStore view code store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩)
    (preserve : ∀ p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀ p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀ p args results answer,
      hooks.call_host p store host args results=.ok answer →
      ∀ value∈answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      Inv out.2.2.1 ∧ CertifiedSupportedStore emission allowed view code out.2.2.1 ∧
      FrameStorePrefix store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
      ∀error,out.1=.Err error → EventfulInvocationError
        (Abs.decode ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL (.mk_uN index.val)::after}::rest,[]⟩)
        (stepHostEvents exec store out) (Store.decodeStore view code out.2.2.1) ambient error ⦄ := by
  have guard : hostStepAddress exec store=some address := by
    rw [hostStepAddress_at exec store frameIndex raw caller compiled (.Call index offset) last hf hi hc fetched]
    exact hostInstructionAddress_direct exec store raw caller compiled index offset address function host addressAt functionAt hostCode
  apply WP.spec_mono (step_host_call_structured_invariant_provenance memory hooks floats allocator allocation interrupts view code
    Inv certify sound exec store platform valid frameIndex raw caller compiled C targets next output ambient f rest index offset after
    address function host expected last hf hi hc fetched addressAt functionAt hostCode binding slots program point machine owned preserve externs issued)
  intro out result
  obtain ⟨newValid,fresh,kept,extension,external,signature,base,pc,front,args,split,pcNext,callActual,causes,effect⟩ := result
  refine ⟨newValid,fresh,kept,extension,?_⟩
  intro error failed
  simp only [stepHostEvents,guard]
  rcases effect with early | observed
  · obtain ⟨error',status,cause,sameStore,empty⟩ := early
    have sameError : error'=error := by simpa only [failed,core.result.Result.Err.injEq] using status.symm
    subst error'
    rw [empty,sameStore]
    exact HostPreparationCause.eventful_error (allocator:=allocator) (hooks:=hooks)
      (exec:={exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}}) (store:=store)
      (platform:=platform) (signature:=signature) (base:=base) cause machine.typed.typed
  · obtain ⟨kind,⟨count,positive,trace⟩,resumed⟩ := observed
    exact host_frame_eventful_error kind trace.erase failed

theorem step_indirect_host_recorded_effects {M P F A : Type} {emission : FunctionEmission} {allowed : instr → Prop}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (Inv : runtime.store.Store M → Prop)
    (certify : ∀ s, Inv s → CertifiedSupportedStore emission allowed view code s)
    (sound : Platform.HostSound hooks Inv (Store.decodeStore view code))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv store)
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
    (owned : Abs.Ownership.StateOwned (Store.ownershipBounds store)
      ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩)
    (preserve : ∀p args results answer,hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀p args results answer,hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀p args results answer,hooks.call_host p store host args results=.ok answer →
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      Inv out.2.2.1 ∧ CertifiedSupportedStore emission allowed view code out.2.2.1 ∧
      FrameStorePrefix store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
      ∀error,out.1=.Err error → EventfulInvocationError
        (Abs.decode ⟨Store.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩)
        (stepHostEvents exec store out) (Store.decodeStore view code out.2.2.1) ambient error ⦄ := by
  apply WP.spec_mono (step_indirect_host_structured_recording memory hooks floats allocator allocation interrupts view code
    Inv certify sound exec store platform valid frameIndex raw inst compiled C targets next output ambient f rest table type after
    position sourceOperands address function host positionSplit selectedSource functionAt hostCode owner last hf hi hc moduleEq
    binding slots program point expected machine owned preserve externs issued)
  intro out result
  refine ⟨result.1,?_⟩
  rcases result.2 with skip | called
  · obtain ⟨guard,fetch,status,sameStore,samePlatform,finalPC,resumed,simulation⟩ := skip
    refine ⟨by rw [sameStore]; exact certify store valid,by rw [sameStore]; exact .refl store,?_,?_⟩
    · rw [sameStore]
      exact Spec.extend_store_refl _ machine.typed.typed.store
    · intro error failed
      rw [status] at failed
      cases failed
  · obtain ⟨guard,signature,base,pc,front,args,split,pcNext,fetch,callActual,fresh,kept,extension,external,causes,effect⟩ := called
    refine ⟨fresh,kept,extension,?_⟩
    intro error failed
    simp only [stepHostEvents,guard]
    rcases effect with early | observed
    · obtain ⟨error',status,cause,sameStore,empty⟩ := early
      have sameError : error'=error := by simpa only [failed,core.result.Result.Err.injEq] using status.symm
      subst error'
      rw [empty,sameStore]
      exact HostPreparationCause.eventful_error (allocator:=allocator) (hooks:=hooks)
        (exec:={exec with frames:=exec.frames.set frameIndex {raw with pc:=pc}}) (store:=store)
        (platform:=platform) (signature:=signature) (base:=base) cause machine.typed.typed
    · obtain ⟨kind,⟨count,positive,trace⟩,resumed⟩ := observed
      exact host_frame_eventful_error kind trace.erase failed
end Exec.Theorems
