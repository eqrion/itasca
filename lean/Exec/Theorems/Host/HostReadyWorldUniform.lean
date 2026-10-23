import Exec.Theorems.Host.HostFrameSiteExecution
import Exec.Theorems.Host.HostDirectWorldUniform
import Exec.Theorems.Composition.Uniform.UniformWorldSource
import Exec.Theorems.Host.HostIndirectWorldUniform
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- A ready host boundary retains enough static and source evidence to execute
the actual direct or indirect call and construct its eventful successor. The
callback transport assumptions remain separate from the source host law. -/
theorem host_ready_world_uniform {M P F A : Type}

    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀ c s,Inv c s → CertifiedSupportedStore view c s)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv code store)
    (expected : List valtype) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (op : instr) (after : List instr)
    (site : HostFrameSite view code exec store expected ambient {f with code:=op::after} rest)
    [StructuredMachine.OrdinaryHeads (emission site.compiled)]
    [StructuredMachine.IndirectProjection (emission site.compiled) site.compiled.indirect.val]
    (kind : DirectHostInstruction store site.raw site.inst site.compiled op ∨
      ∃table type : U32,op=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val) ∧
        SourceIndirectHostBoundary store ⟨Store.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩)
    (callback : ∀ p host args results,
      hooks.call_host p store host args results ⦃ answer => ∃ afterCode,
        Store.CodeAgreesOn store code afterCode ∧ Inv afterCode answer.2.2.1 ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode answer.2.2.1) ∧
        Store_ok (Store.decodeStore view afterCode answer.2.2.1) ⦄)
    (preserve : ∀p host args results answer,hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀p host args results answer,hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀p host args results answer,hooks.call_host p store host args results=.ok answer →
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      UniformWorldSourceSuccess (view:=view)
        Inv code expected store
        ⟨Store.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩ site.raw.pc.val false out ⦄ := by
  rcases kind with direct | indirect
  · obtain ⟨index,offset,address,function,host,source,fetch,addressAt,functionAt,hostCode⟩ := direct
    subst op
    apply WP.spec_mono (step_host_call_world_uniform memory hooks floats allocator allocation interrupts view code Inv certify exec store platform valid
      site.index site.raw site.inst site.compiled site.context site.targets site.next site.output ambient f rest index offset after address function host expected
      site.last site.frameAt site.instanceAt site.compiledAt fetch addressAt functionAt hostCode site.binding site.slots site.program site.point site.machine
      (site.eventful (certify code store valid) platform).owned (fun p=>callback p host) (fun p=>preserve p host) (fun p=>externs p host) (fun p=>issued p host))
    intro out result
    exact UniformWorldSourceSuccess.unbundle result
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
    apply WP.spec_mono (step_indirect_host_world_uniform memory hooks floats allocator allocation interrupts view code Inv certify exec store platform valid
      site.index site.raw site.inst site.compiled site.context site.targets site.next site.output ambient f rest table type after position operands
      ⟨store.id,address⟩ function host positionSplit resolved functionAt hostCode rfl site.last site.frameAt site.instanceAt site.compiledAt site.moduleEq
      site.binding site.slots site.program site.point expected site.machine (site.eventful (certify code store valid) platform).owned
      (fun p=>callback p host) (fun p=>preserve p host) (fun p=>externs p host) (fun p=>issued p host))
    intro out result
    exact UniformWorldSourceSuccess.unbundle result
end Exec.Theorems
