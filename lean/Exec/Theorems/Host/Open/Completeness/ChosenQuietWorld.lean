import Exec.Theorems.Host.Open.Completeness.CompletedChosenWorld
import Exec.Spec.Choices.HostIrrelevant
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- The open driver preserves a selected scalar/SIMD/growth policy during a
completed silent Wasm dispatch. Its atomic host policy is irrelevant: actual
host entry is represented by a separate suspended combined transition. -/
def ChosenQuietWorldResult {M F A : Type} (choices : Spec.SourceChoices) (occurrence : Nat)
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (world : EventfulWorld Executable.emission Abs.ExecutableInstr M Unit view expected) (out : Answer M Unit) : Prop:=
  match out.1 with
  | .Ok _=>∃next : EventfulWorld Executable.emission Abs.ExecutableInstr M Unit view expected,
      ExecutableInv view next.code next.machine.store ∧ out=(.Ok (),next.machine.exec,next.machine.store,next.machine.platform) ∧
      ChosenConcreteSim choices occurrence U32.max world.machine.pc next.machine.pc world.machine.pending next.machine.pending world.machine.source next.machine.source ∧
      ReentrantCallbacks.Effect view world.code world.machine.store next.code next.machine.store ∧
      next.machine.source.ambient=world.machine.source.ambient
  | .Err error=>∃afterCode,ReentrantCallbacks.Effect view world.code world.machine.store afterCode out.2.2.1 ∧
      ChosenEventfulInvocationError choices occurrence (Abs.decode world.machine.source) []
        (Store.decodeStore view afterCode out.2.2.1) world.machine.source.ambient error ∧
      EventfulDispatchCause memory (inert memory) floats allocator world.machine out error

theorem chosen_quiet_world {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Spec.firstNumericChoice) (vector : choices.vector=Spec.firstVectorChoice)
    (occurrence : Nat) {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    {expected : List valtype}
    (world : EventfulWorld Executable.emission Abs.ExecutableInstr M Unit view expected)
    (held : ExecutableInv view world.code world.machine.store) (active : 0<world.machine.exec.frames.length)
    (typed : Config_ok (Abs.decode world.machine.source) (.mk_list expected)) (out : Answer M Unit)
    (prepared : prepareStep memory (inert memory) floats allocator world.machine.exec world.machine.store world.machine.platform=.ok (.done out)) :
    ChosenQuietWorldResult choices occurrence memory floats allocator world out := by
  let silentChoices : Spec.SourceChoices:={choices with host:=Spec.trappingHostChoice}
  have selected : silentChoices.Admissible:=⟨Spec.trappingHostChoice_admissible,admissible.numeric,admissible.vector,admissible.memory,admissible.table⟩
  have growth : GrowthChoicesCompatible memory allocator view silentChoices:=⟨compatible.memoryReply,compatible.tableReply⟩
  have restore : {silentChoices with host:=choices.host}=choices:=by cases choices;rfl
  obtain ⟨post,quiet⟩:=completed_chosen_world selected numericChoice vector rfl occurrence memory floats allocator correct allocation view laws growth world held active typed out prepared
  cases status : out.1 with
  | Ok unit=>
    simp only [ChosenWorldStepResult,status] at post
    simp only [ChosenQuietWorldResult,status]
    obtain ⟨next,fresh,same,edge⟩:=post
    have simulation:=edge.selected
    rw [quiet] at simulation
    have concrete : ChosenConcreteSim choices occurrence U32.max world.machine.pc next.machine.pc world.machine.pending next.machine.pending
        world.machine.source next.machine.source:=by
      rcases simulation with ⟨sameSource,sameOccurrence,empty,decrease⟩|⟨count,positive,advanced,path⟩
      · exact .inl ⟨sameSource,decrease⟩
      · exact .inr ⟨count,positive,by simpa only [restore] using path.quiet_host_irrelevant choices.host⟩
    exact ⟨next.toEventfulWorld,fresh.1,same,concrete,
      ⟨⟨edge.recorded.edge.agrees,fresh.1,edge.recorded.edge.metadata,edge.recorded.edge.extension⟩,fresh.2⟩,edge.recorded.edge.ambient⟩
  | Err error=>
    simp only [ChosenWorldStepResult,ChosenWorldSourceStepResult,status] at post
    simp only [ChosenQuietWorldResult,status]
    obtain ⟨afterCode,fresh,certified,metadata,agrees,extension,path,cause⟩:=post
    rw [quiet] at path
    have actualCause:=(completed_world_causes memory floats allocator correct allocation view laws world held active out prepared).2 error status
    refine ⟨afterCode,⟨⟨agrees,fresh.1,metadata,extension⟩,fresh.2⟩,?_,actualCause⟩
    cases error <;> simp only [ChosenEventfulInvocationError] at path ⊢
    · obtain ⟨count,steps⟩:=path
      exact ⟨count,by simpa only [restore] using steps.quiet_host_irrelevant choices.host⟩
    · obtain ⟨body,count,steps⟩:=path
      exact ⟨body,count,by simpa only [restore] using steps.quiet_host_irrelevant choices.host⟩
    · obtain ⟨body,count,steps⟩:=path
      exact ⟨body,count,by simpa only [restore] using steps.quiet_host_irrelevant choices.host⟩
end Exec.Theorems.OpenReentrantControl
