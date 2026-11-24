import Itasca.Runtime.Interp.Recording
import Itasca.Runtime.Integration.Host.HostIndirectStructuredWorld
import Itasca.Runtime.Integration.Host.HostIndirectSelected
import Itasca.Runtime.Integration.Execution.World.Loop
import Itasca.Runtime.Interp.Relations.ResourceCausesAndArgumentErrors
import Itasca.Runtime.Integration.Host.HostRecordingBoundary
import Itasca.Runtime.Interp.Relations.StepActive

open Itasca.Representation

/-!
# Host-call world outcomes

Direct and indirect host calls construct the source/machine result for the selected site while retaining actual events and the post-call code interpretation.
-/

/-! ## HostDirectWorld -/

section HostDirectWorld

/-!
# Direct host calls in evolving worlds

Direct host-call outcomes preserve the evolving-world interpretation and actual callback events. The host-site join combines these with indirect calls.
-/

namespace Itasca.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Interp
open Itasca.Interp.Machine
theorem step_host_call_world_outcomes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀ c s, Inv c s → CertifiedSupportedStore view c s)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv code store)
    (frameIndex : Usize) (raw : runtime.interp.Frame)
    (caller : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (index offset : U32) (after : List instr)
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
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Representation.decodeStore view code store) raw
      {f with code := .CALL (.mk_uN index.val)::after} compiled C targets next output)
    (machine : Execution view code store exec
      ⟨Representation.decodeStore view code store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩ expected raw.pc.val false)
    (owned : SourceMachine.Ownership.StatefulOwned (Store.ownershipBounds store)
      ⟨Representation.decodeStore view code store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩)
    (callback : ∀ p args results,
      hooks.call_host p store host args results ⦃ (result, nextPlatform, after, returned) => ∃ afterCode,
        Store.CodeAgreesOn store code afterCode ∧ Inv afterCode after ∧
        Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view afterCode after) ∧
        Store_ok (Representation.decodeStore view afterCode after) ⦄div)
    (retains : HostRetention hooks store host) :
    let before : EventfulWorld M P view expected :=
      ⟨code,⟨store,exec,platform,
        ⟨Representation.decodeStore view code store,ambient,{f with code:=.CALL (.mk_uN index.val)::after}::rest,[]⟩,
        raw.pc.val,false,machine,certify code store valid,owned⟩⟩
    Computation.DivSpec (HostDiverges hooks store) (runtime.interp.step memory hooks floats allocator exec store platform)
      fun out => WorldStepResult memory hooks floats allocator Inv before out := by
  let before : EventfulMachine M P view code expected :=
    ⟨store,exec,platform,
      ⟨Representation.decodeStore view code store,ambient,{f with code:=.CALL (.mk_uN index.val)::after}::rest,[]⟩,
      raw.pc.val,false,machine,certify code store valid,owned⟩
  have guard : hostStepAddress exec store=some address := by
    rw [host_step_address_at exec store frameIndex raw caller compiled (.Call index offset) last hf hi hc fetched]
    exact host_instruction_address_direct exec store raw caller compiled index offset address function host addressAt functionAt hostCode
  rcases (step_host_call_structured_world_provenance memory hooks floats allocator allocation interrupts
      view code Inv certify exec store platform valid frameIndex raw caller compiled C targets next output ambient f rest
      index offset after address function host expected last hf hi hc fetched addressAt functionAt hostCode binding slots
      program point machine owned.values callback retains).imp_exists with
      ⟨⟨status,afterExec,afterStore,afterPlatform⟩,actual,afterCode,agrees,freshInv,fresh,
      retained,extension,external,signature,base,pc,front,args,split,pcNext,site,callActual,causes,effect⟩ | ⟨actual,diverged⟩
  swap
  · dsimp only
    rw [actual]
    exact .div _ diverged
  dsimp only
  rw [actual,Computation.DivSpec.ok_iff]
  have same := Store.decode_store_code_agrees view agrees
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
end Itasca.Integration

end HostDirectWorld

/-! ## HostIndirectWorld -/

section HostIndirectWorld

/-!
# Indirect host calls in evolving worlds

Actual indirect host dispatch chooses a post-call code interpretation and retains the source/machine outcome under the world callback contract.
-/

namespace Itasca.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Interp
open Itasca.Interp.Machine
theorem step_indirect_host_world_outcomes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀ c s, Inv c s → CertifiedSupportedStore view c s)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv code store)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [IndirectProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (table type : U32) (after : List instr)
    (position : Nat) (sourceOperands : List val) (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (host : U64)
    (positionSplit : f.vals=sourceOperands++[SourceMachine.integerVal .I32 position])
    (selectedSource : SourceMachine.Indirect.resolve (Representation.decodeStore view code store) f table.val type.val position=some address.index.val)
    (functionAt : store.funcs.val[address.index.val]?=some function) (hostCode : function.code=.Host host)
    (owner : address.store=store.id)
    (last : frameIndex.val+1=exec.frames.length) (hf : exec.frames.val[frameIndex.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst) (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module=Representation.decodeInstance store inst)
    (binding : FrameBinding store exec raw f) (slots : FrameSlots exec raw f)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Representation.decodeStore view code store) raw
      {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Representation.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩ expected raw.pc.val false)
    (owned : SourceMachine.Ownership.StatefulOwned (Store.ownershipBounds store)
      ⟨Representation.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩)
    (callback : ∀ p args results,
      hooks.call_host p store host args results ⦃ (result, nextPlatform, after, returned) => ∃ afterCode,
        Store.CodeAgreesOn store code afterCode ∧ Inv afterCode after ∧
        Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view afterCode after) ∧
        Store_ok (Representation.decodeStore view afterCode after) ⦄div)
    (retains : HostRetention hooks store host) :
    let before : EventfulWorld M P view expected :=
      ⟨code,⟨store,exec,platform,
        ⟨Representation.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩,
        raw.pc.val,false,machine,certify code store valid,owned⟩⟩
    Computation.DivSpec (HostDiverges hooks store) (runtime.interp.step memory hooks floats allocator exec store platform)
      fun out => WorldStepResult memory hooks floats allocator Inv before out := by
  let before : EventfulMachine M P view code expected :=
    ⟨store,exec,platform,
      ⟨Representation.decodeStore view code store,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩,
      raw.pc.val,false,machine,certify code store valid,owned⟩
  rcases (step_indirect_host_structured_world memory hooks floats allocator allocation interrupts view code Inv certify exec store platform valid
      frameIndex raw inst compiled C targets next output ambient f rest table type after position sourceOperands address function host
      positionSplit selectedSource functionAt hostCode owner last hf hi hc moduleEq binding slots program point expected machine owned.values callback retains).imp_exists with
      ⟨⟨status,afterExec,afterStore,afterPlatform⟩,actual,outcome⟩ | ⟨actual,diverged⟩
  swap
  · dsimp only
    rw [actual]
    exact .div _ diverged
  dsimp only
  rw [actual,Computation.DivSpec.ok_iff]
  rcases outcome with skip | called
  · obtain ⟨guard,fetch,success,sameStore,samePlatform,finalPC,resumed,simulation⟩ := skip
    change status=.Ok () at success
    subst status
    change afterStore=store at sameStore
    change afterPlatform=platform at samePlatform
    subst afterStore
    subst afterPlatform
    let final : EventfulMachine M P view code expected :=
      ⟨store,afterExec,platform,before.source,finalPC,false,resumed,certify code store valid,owned⟩
    have edge : EventfulTransition memory hooks floats allocator before [] final :=
      ⟨actual,(simulation.widen program.fetchBound).eventful,
        Spec.extend_store_refl _ machine.typed.typed.store,.refl store,rfl⟩
    refine ⟨⟨code,final⟩,valid,rfl,?_⟩
    simpa only [stepHostEvents,guard,before] using edge.world
  · obtain ⟨afterCode,agrees,freshInv,guard,signature,base,pc,front,args,split,pcNext,fetch,callActual,
        fresh,retained,extension,external,site,causes,effect⟩ := called
    have same := Store.decode_store_code_agrees view agrees
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
          (args++[SourceMachine.integerVal .I32 position]) (afterExec.host_results.val.map sourceValue) after finalPC
          (by simp only [EventfulMachine.change_code,before,same])
          (by simpa only [List.append_assoc] using split) actual retained external
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
end Itasca.Integration

end HostIndirectWorld

/-! ## HostSiteWorld -/

section HostSiteWorld

/-! ## HostReadyWorld -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Interp

/-- A ready host boundary retains enough static and source evidence to execute
the actual direct or indirect call and construct its eventful successor. The
callback transport assumptions remain separate from the source host law. -/
theorem host_ready_world_outcomes {M P F A : Type}

    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀ c s,Inv c s → CertifiedSupportedStore view c s)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv code store)
    (expected : List valtype) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (op : instr) (after : List instr)
    (site : HostFrameSite view code exec store expected ambient {f with code:=op::after} rest)
    [Machine.OrdinaryHeads (emission site.compiled)]
    [Machine.IndirectProjection (emission site.compiled) site.compiled.indirect.val]
    (kind : DirectHostInstruction store site.raw site.inst site.compiled op ∨
      ∃table type : U32,op=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val) ∧
        SourceIndirectHostBoundary store ⟨Representation.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩)
    (callback : ∀ p host args results,
      hooks.call_host p store host args results ⦃ (result, nextPlatform, after, returned) => ∃ afterCode,
        Store.CodeAgreesOn store code afterCode ∧ Inv afterCode after ∧
        Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view afterCode after) ∧
        Store_ok (Representation.decodeStore view afterCode after) ⦄div)
    (retains : ∀ host, HostRetention hooks store host) :
    Computation.DivSpec (HostDiverges hooks store) (runtime.interp.step memory hooks floats allocator exec store platform) fun out =>
      WorldSourceStepResult (view:=view)
        memory hooks floats allocator Inv code expected exec store platform
        ⟨Representation.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩ site.raw.pc.val false out := by
  rcases kind with direct | indirect
  · obtain ⟨index,offset,address,function,host,source,fetch,addressAt,functionAt,hostCode⟩ := direct
    subst op
    apply Computation.DivSpec.mono (step_host_call_world_outcomes memory hooks floats allocator allocation interrupts view code Inv certify exec store platform valid
      site.index site.raw site.inst site.compiled site.context site.targets site.next site.output ambient f rest index offset after address function host expected
      site.last site.frameAt site.instanceAt site.compiledAt fetch addressAt functionAt hostCode site.binding site.slots site.program site.point site.machine
      (site.eventful (certify code store valid) platform).owned (fun p=>callback p host) (retains host))
    intro out result
    exact result.unbundle
  · obtain ⟨table,type,source,boundary⟩ := indirect
    subst op
    obtain ⟨other,callers,sourceTable,Itasca.Translation.valueType,position,sourceAfter,operands,address,function,host,frames,split,bounded,selected,functionAt,hostCode⟩ := boundary
    change {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest =
      {other with code:=.CALL_INDIRECT (.mk_uN sourceTable) (.mk_uN Itasca.Translation.valueType)::sourceAfter}::callers at frames
    obtain ⟨frameEq,restEq⟩ := List.cons.inj frames
    have codeEq := congrArg SourceMachine.AFrame.code frameEq
    simp only [List.cons.injEq,instr.CALL_INDIRECT.injEq,uN.mk_uN.injEq] at codeEq
    obtain ⟨⟨tableEq,typeEq⟩,tailEq⟩ := codeEq
    have positionSplit : f.vals=operands++[SourceMachine.integerVal .I32 position] := (congrArg SourceMachine.AFrame.vals frameEq).trans split
    have resolved : SourceMachine.Indirect.resolve (Representation.decodeStore view code store) f table.val type.val position=some address.val := by
      change SourceMachine.Indirect.resolve (Representation.decodeStore view code store)
        {other with code:=.CALL_INDIRECT (.mk_uN sourceTable) (.mk_uN Itasca.Translation.valueType)::sourceAfter}
        sourceTable Itasca.Translation.valueType position=some address.val at selected
      rw [←frameEq,←tableEq,←typeEq] at selected
      exact selected
    apply Computation.DivSpec.mono (step_indirect_host_world_outcomes memory hooks floats allocator allocation interrupts view code Inv certify exec store platform valid
      site.index site.raw site.inst site.compiled site.context site.targets site.next site.output ambient f rest table type after position operands
      ⟨store.id,address⟩ function host positionSplit resolved functionAt hostCode rfl site.last site.frameAt site.instanceAt site.compiledAt site.moduleEq
      site.binding site.slots site.program site.point expected site.machine (site.eventful (certify code store valid) platform).owned
      (fun p=>callback p host) (retains host))
    intro out result
    exact result.unbundle
end Itasca.Integration

end

/-! ## HostSiteWorld -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std Itasca.Interp

/-- All normalized direct and indirect host sites return normally. Successful
results retain the exact eventful advance, including source-only prefixes. The
raw retention and issuance premises are explicit conditional embedding laws. -/
theorem StructuredHostSite.world_outcomes {M P F A : Type}

    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀ c s,Inv c s → CertifiedSupportedStore view c s)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv code store)
    (callback : ∀ host p args results,
      hooks.call_host p store host args results ⦃ (result, nextPlatform, after, returned) => ∃ afterCode,
        Store.CodeAgreesOn store code afterCode ∧ Inv afterCode after ∧
        Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view afterCode after) ∧
        Store_ok (Representation.decodeStore view afterCode after) ⦄div)
    (retains : ∀ host, HostRetention hooks store host)
    {expected : List valtype} {pc : Nat} {pending : Bool} {source : SourceMachine.AState}
    (site : StructuredHostSite view code exec store expected pc pending source)
    (typed : SourceMachine.ATyped source) :
    Computation.DivSpec (HostDiverges hooks store) (runtime.interp.step memory hooks floats allocator exec store platform) fun out =>
      WorldSourceStepResult (view:=view)
        memory hooks floats allocator Inv code expected exec store platform source pc pending out := by
  induction site with
  | @ready ambient f rest op after site kind =>
    exact host_ready_world_outcomes memory hooks floats allocator allocation interrupts view code Inv certify
      exec store platform valid expected ambient f rest op after site kind
      (fun p host => callback host p) retains
  | @normalize count pc s ambient before middle rest chain site ih =>
    apply Computation.DivSpec.mono (ih (chain.sound s ambient rest typed).1)
    intro out result
    exact result.prepend_normalization chain typed
end Itasca.Integration

end

end HostSiteWorld
