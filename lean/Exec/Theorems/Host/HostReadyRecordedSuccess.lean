import Exec.Theorems.Host.HostFrameSiteExecution
import Exec.Theorems.Host.HostDirectRecordedSuccess
import Exec.Theorems.Host.HostIndirectRecordedSuccess
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- A ready host boundary retains enough static and source evidence to execute
the actual direct or indirect call and construct its eventful successor. The
callback transport assumptions remain separate from the source host law. -/
theorem host_ready_recorded_success {M P F A : Type}
    {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (Inv : runtime.store.Store M → Prop)
    (certify : ∀s,Inv s → CertifiedSupportedStore emission allowed view code s)
    (sound : Platform.HostSound hooks Inv (Store.decodeStore view code))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv store)
    (expected : List valtype) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (op : instr) (after : List instr)
    (site : HostFrameSite emission allowed view code exec store expected ambient {f with code:=op::after} rest)
    [StructuredMachine.OrdinaryHeads (emission site.compiled)]
    [StructuredMachine.IndirectProjection (emission site.compiled) site.compiled.indirect.val]
    (kind : DirectHostInstruction store site.raw site.inst site.compiled op ∨
      ∃table type : U32,op=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val) ∧
        SourceIndirectHostBoundary store ⟨Store.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩)
    (preserve : ∀p host args results answer,hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀p host args results answer,hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀p host args results answer,hooks.call_host p store host args results=.ok answer →
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      Inv out.2.2.1 ∧ (out.1=.Ok () → ∃events,∃final : EventfulMachine emission allowed M P view code expected,
        out=(.Ok (),final.exec,final.store,final.platform) ∧
        RecordedEventfulTransition memory hooks floats allocator (site.eventful (certify store valid) platform) events final) ⦄ := by
  rcases kind with direct | indirect
  · obtain ⟨index,offset,address,function,host,source,fetch,addressAt,functionAt,hostCode⟩ := direct
    subst op
    apply WP.spec_mono (step_host_call_recorded_success memory hooks floats allocator allocation interrupts view code Inv certify sound exec store platform valid
      site.index site.raw site.inst site.compiled site.context site.targets site.next site.output ambient f rest index offset after address function host expected
      site.last site.frameAt site.instanceAt site.compiledAt fetch addressAt functionAt hostCode site.binding site.slots site.program site.point site.machine
      (site.eventful (certify store valid) platform).owned (fun p=>preserve p host) (fun p=>externs p host) (fun p=>issued p host))
    intro out result
    refine ⟨result.1,?_⟩
    intro success
    obtain ⟨final,equal,edge⟩ := result.2 success
    exact ⟨_,final,equal,edge⟩
  · obtain ⟨table,type,source,boundary⟩ := indirect
    subst op
    obtain ⟨other,callers,sourceTable,sourceType,position,sourceAfter,operands,address,function,host,frames,split,bounded,selected,functionAt,hostCode⟩ := boundary
    change {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest =
      {other with code:=.CALL_INDIRECT (.mk_uN sourceTable) (.mk_uN sourceType)::sourceAfter}::callers at frames
    obtain ⟨frameEq,restEq⟩ := List.cons.inj frames
    have codeEq := congrArg Abs.AFrame.code frameEq
    simp only [List.cons.injEq,instr.CALL_INDIRECT.injEq,uN.mk_uN.injEq] at codeEq
    obtain ⟨⟨tableEq,typeEq⟩,tailEq⟩ := codeEq
    have positionSplit : f.vals=operands++[Abs.integerVal .I32 position] := (congrArg Abs.AFrame.vals frameEq).trans split
    have resolved : Abs.Indirect.resolve (Store.decodeStore view code store) f table.val type.val position=some address.val := by
      change Abs.Indirect.resolve (Store.decodeStore view code store)
        {other with code:=.CALL_INDIRECT (.mk_uN sourceTable) (.mk_uN sourceType)::sourceAfter}
        sourceTable sourceType position=some address.val at selected
      rw [←frameEq,←tableEq,←typeEq] at selected
      exact selected
    exact step_indirect_host_recorded_success memory hooks floats allocator allocation interrupts view code Inv certify sound exec store platform valid
      site.index site.raw site.inst site.compiled site.context site.targets site.next site.output ambient f rest table type after position operands
      ⟨store.id,address⟩ function host positionSplit resolved functionAt hostCode rfl site.last site.frameAt site.instanceAt site.compiledAt site.moduleEq
      site.binding site.slots site.program site.point expected site.machine (site.eventful (certify store valid) platform).owned
      (fun p=>preserve p host) (fun p=>externs p host) (fun p=>issued p host)
end Exec.Theorems
