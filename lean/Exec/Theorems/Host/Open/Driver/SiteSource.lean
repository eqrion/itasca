import Exec.Interp.Relations.ErasedChosen
import Exec.Theorems.Host.Open.Driver.DirectSource
import Exec.Theorems.Host.Open.Driver.IndirectSource
import Exec.Theorems.Host.Open.Driver.PendingSite
import Exec.Theorems.Host.HostFrameSiteExecution
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall Exec.Interp.StructuredMachine

theorem PreparedSourceHost.prepend {M P : Type} {emission : FunctionEmission} {allowed : instr → Prop}
    {memory : runtime.platform.MemoryBuffer M} {exec : runtime.interp.Execution} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {first middle : config} {expected : resulttype} {phase : CallPhase M P}
    (head : StepsH first [] middle) (chosenHead : Spec.UniversalQuietPrefix first middle) (post : PreparedSourceHost emission allowed memory view code store exec middle expected phase) :
    PreparedSourceHost emission allowed memory view code store exec first expected phase := by
  cases phase with
  | done answer => exact post
  | pending exec after token address base identity args defaults =>
    obtain ⟨hostArgs,argsOwned,pending,beforeEq,addressEq,identityEq,argsEq,tail,typed,completion,chosen,saved⟩ := post
    exact ⟨hostArgs,argsOwned,pending,beforeEq,addressEq,identityEq,argsEq,Spec.stepsH_trans head tail,typed,completion,chosenHead.trans chosen,saved⟩

private theorem normalization_quiet {count : Nat} {before after : Abs.AFrame}
    (chain : ErasedSteps count before after) (s : store) (ambient : frame) (rest : List Abs.AFrame)
    (typed : Abs.ATyped ⟨s,ambient,before::rest,[]⟩) :
    StepsH (Abs.decode ⟨s,ambient,before::rest,[]⟩) [] (Abs.decode ⟨s,ambient,after::rest,[]⟩) := by
  rcases (chain.sound s ambient rest typed).2 with ⟨_,rfl⟩ | ⟨same,decrease⟩ | ⟨count,positive,steps⟩
  · exact .refl typed.decode_wf
  · rw [←same]; exact .refl typed.decode_wf
  · exact steps.erase

/-- Actual native preparation at a typed source host site exposes its source
request through all source-only control normalization. -/
theorem prepare_site_source {M P F A : Type} {emission : FunctionEmission} {allowed : instr → Prop}
    [∀compiled,OrdinaryHeads (emission compiled)] [∀compiled,IndirectProjection (emission compiled) compiled.indirect.val]
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀p,hooks.interrupt p ⦃ _=>True⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (shaped : Store.Shape view store)
    {expected : List valtype} {pc : Nat} {pending : Bool} {source : Abs.AState}
    (site : StructuredHostSite emission allowed view code exec store expected pc pending source)
    (typed : Abs.ATyped source) (configurationTyped : Config_ok (Abs.decode source) (.mk_list expected)) :
    prepareStep memory hooks floats allocator exec store platform
      ⦃phase=>PreparedSourceHost emission allowed memory view code store exec (Abs.decode source) (.mk_list expected) phase⦄ := by
  induction site with
  | @ready ambient f rest op after site kind =>
    rcases kind with direct|indirect
    · obtain ⟨index,offset,address,function,host,sourceEq,fetch,addressAt,functionAt,hostCode⟩ := direct
      subst op
      exact prepare_direct_host_source memory hooks floats allocator allocation interrupts view code exec store platform
        site.index site.raw site.inst site.compiled site.context site.targets site.next site.output ambient f rest index offset after address function host expected
        site.last site.frameAt site.instanceAt site.compiledAt fetch addressAt functionAt hostCode site.binding site.slots site.program site.point site.machine site.owned configurationTyped
    · obtain ⟨table,type,sourceEq,boundary⟩ := indirect
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
      exact prepare_indirect_host_source memory hooks floats allocator allocation interrupts view code exec store platform shaped
        site.index site.raw site.inst site.compiled site.context site.targets site.next site.output ambient f rest table type after position operands
        ⟨store.id,address⟩ function host positionSplit resolved functionAt hostCode rfl site.last site.frameAt site.instanceAt site.compiledAt site.moduleEq
        site.binding site.slots site.program site.point expected site.machine site.owned configurationTyped
  | @normalize count pc s ambient before middle rest chain site ih =>
    have quiet := normalization_quiet chain s ambient rest typed
    apply WP.spec_mono (ih (chain.sound s ambient rest typed).1 (Spec.stepsH_config_preserved quiet configurationTyped))
    intro phase post
    exact post.prepend quiet (by
      intro choices admissible vector occurrence
      obtain ⟨count,prefixSteps,bounded⟩:=chain.chosen admissible vector occurrence s ambient rest typed
      exact ⟨count,prefixSteps⟩)

/-- A concrete suspension has the same address, identity and copied arguments
as one independently typed source request, before any host reply is assumed. -/
theorem pending_source {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    {expected : List valtype}
    (world : EventfulWorld Executable.emission Abs.ExecutableInstr M Unit view expected)
    (held : ExecutableInv view world.code world.machine.store) (active : 0<world.machine.exec.frames.length)
    (configurationTyped : Config_ok (Abs.decode world.machine.source) (.mk_list expected))
    (ready : runtime.interp.Execution) (after : runtime.store.Store M) (token : Unit)
    (address : runtime.FuncAddr) (base : Usize) (identity : U64) (args defaults : alloc.vec.Vec runtime.Value)
    (pending : prepareStep memory (inert memory) floats allocator world.machine.exec world.machine.store world.machine.platform=
      .ok (.pending ready after token address base identity args defaults)) :
    PreparedSourceHost Executable.emission Abs.ExecutableInstr memory view world.code world.machine.store world.machine.exec (Abs.decode world.machine.source) (.mk_list expected)
      (.pending ready after token address base identity args defaults) := by
  have site := pending_source_site memory floats allocator correct allocation view laws world held active ready after token address base identity args defaults pending
  have total := prepare_site_source memory (inert memory) floats allocator allocation (fun _=>WP.spec.ret trivial)
    view world.code world.machine.exec world.machine.store world.machine.platform held.shape site world.machine.invariant.typed.typed configurationTyped
  rw [pending,WP.spec_ok] at total
  exact total
end Exec.Theorems.OpenReentrantControl
