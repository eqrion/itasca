import Exec.Theorems.Host.Open.Source.Chosen.ControlChoices
import Exec.Theorems.Host.Open.Source.Control.Publication
import Exec.Abs.Sim.OpenContextChosenTrap
import Exec.Spec.Open.ExecutionCompression
import Exec.Spec.Open.ExecutionChosenCounted
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- This same concrete looping selector has an actual divergent synchronous
callback and a productive selected combined source stream of host actions. -/
theorem chosen_loop_example {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (publication : SourcePublication) (owner : Usize)
    (stop : Spec.OpenExecution.StopReason → config → Prop) (choices : SourceOperationChoices)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) (identity : U64) (args defaults : Slice runtime.Value)
    (occurrence : Nat) (stack : List (Spec.OpenExecution.Continuation SourceControl)) :
    (platform memory floats allocator (fun _ _=>[.jump 0])).call_host () store identity args defaults=.div ∧
    Spec.OpenExecution.ChoiceInfinite (sourceModel view publication (fun _ _=>[.jump 0]) owner stop)
      (sourceControlChoices choices) occurrence
      ⟨Store.decodeStore view code store,
        .host (.active ⟨0,[.jump 0],identity.val,args.val.map sourceValue⟩),stack⟩ := by
  refine ⟨looping_platform_diverges memory floats allocator store identity args defaults,?_⟩
  exact ⟨fun _=>_,fun _=>[.hostAction],rfl,fun _=>.action rfl⟩

/-- A source-only finite host/Wasm/host reentry trace. A chosen quiet source
prefix describes the Wasm wrapper's host request; native return is not a premise.
The inner trap propagates to the outer host while retaining nested observations. -/
theorem chosen_finite_reentry_example {M : Type} (view : M → Slice U8)
    (publication : SourcePublication) (select : Selector) (owner : Usize)
    (stop : Spec.OpenExecution.StopReason → config → Prop) (choices : SourceOperationChoices)
    (s : store) (typedStore : Store_ok s) (index : Usize)
    (bound : index.val<s.FUNCS.length)
    (signature : s.FUNCS[index.val]!.TYPE=.mk_functype (.mk_list []) (.mk_list []))
    (pending : Spec.OpenHost.Pending) (beforeEq : pending.before=s)
    (typedPending : Config_ok pending.initial (.mk_list []))
    (quietCount occurrence : Nat)
    (quiet : Spec.ChosenStepsN choices.wasm (occurrence+2) quietCount
      ⟨⟨s,Spec.invocationFrame⟩,[.CALL_ADDR index.val]⟩ [] pending.initial)
    (innerInstruction : (sourceHostEntry select owner pending.identity pending.arguments).code[0]?=some .trapped)
    (outerIdentity : Nat) (outerArgs : List val)
    (stack : List (Spec.OpenExecution.Continuation SourceControl)) :
    ∃count events,Spec.OpenExecution.ChoiceTrace (sourceModel view publication select owner stop)
      (sourceControlChoices choices) occurrence count
      ⟨s,.host (.active ⟨0,[.invoke index (Slice.new _) 1],outerIdentity,outerArgs⟩),stack⟩ events
      ⟨s,.hostReturn none,stack⟩ ∧
      .invokeEnter index.val []∈events ∧ .hostEnter pending.address pending.identity pending.arguments∈events := by
  let model:=sourceModel view publication select owner stop
  let outer : SourceControl:=.active ⟨0,[.invoke index (Slice.new _) 1],outerIdentity,outerArgs⟩
  let caller : SourceControl:=.active ⟨1,[.invoke index (Slice.new _) 1],outerIdentity,outerArgs⟩
  let suspended : Spec.OpenExecution.Suspension:=⟨pending,.mk_list [],typedPending⟩
  let position:=occurrence+2+quietCount
  have request : Spec.OpenExecution.ChoiceTransition model (sourceControlChoices choices) occurrence
      ⟨s,.host outer,stack⟩ [.invokeEnter index.val []]
      ⟨s,.invokeRequest index.val [] [] [],.host caller::stack⟩ :=
    .requestInvoke rfl bound signature
  have accepted : Spec.OpenExecution.ChoiceTransition model (sourceControlChoices choices) (occurrence+1)
      ⟨s,.invokeRequest index.val [] [] [],.host caller::stack⟩ []
      ⟨s,.wasm Spec.invocationFrame [.CALL_ADDR index.val] (.mk_list []),.host caller::stack⟩ := .acceptInvoke .nil
  have normalized:=Spec.OpenExecution.ChoiceTrace.wasmCounted model (sourceControlChoices choices) quiet (.mk_list []) (.host caller::stack)
  have enter : Spec.OpenExecution.ChoiceTransition model (sourceControlChoices choices) position
      ⟨s,.wasm pending.initial.1.2 pending.initial.2 (.mk_list []),.host caller::stack⟩
      [.hostEnter pending.address pending.identity pending.arguments]
      ⟨s,.host (.active (sourceHostEntry select owner pending.identity pending.arguments)),.wasm suspended::.host caller::stack⟩ := by
    have raw:=Spec.OpenExecution.ChoiceTransition.enter (model := model) (choices := sourceControlChoices choices)
      (occurrence := position) (stack := .host caller::stack) suspended rfl (Spec.OpenExecution.pending_store pending).symm rfl
    change Spec.OpenExecution.ChoiceTransition model (sourceControlChoices choices) position
      ⟨pending.initial.1.1,.wasm pending.initial.1.2 pending.initial.2 (.mk_list []),.host caller::stack⟩
      [.hostEnter pending.address pending.identity pending.arguments]
      ⟨pending.initial.1.1,.host (.active (sourceHostEntry select owner pending.identity pending.arguments)),.wasm suspended::.host caller::stack⟩ at raw
    have pendingStore : pending.initial.1.1=s:=(Spec.OpenExecution.pending_store pending).trans beforeEq
    rw [pendingStore] at raw
    exact raw
  have trapped : Spec.OpenExecution.ChoiceTransition model (sourceControlChoices choices) (position+1)
      ⟨s,.host (.active (sourceHostEntry select owner pending.identity pending.arguments)),.wasm suspended::.host caller::stack⟩ [.hostAction]
      ⟨s,.host (.draft none),.wasm suspended::.host caller::stack⟩ := by
    apply Spec.OpenExecution.ChoiceTransition.action
    have instruction : (sourceSelector select owner pending.identity pending.arguments)[0]?=some .trapped:=innerInstruction
    simp only [sourceControlChoices,chosenSourceAction,sourceHostEntry,instruction]
  have exited : Spec.OpenExecution.ChoiceTransition model (sourceControlChoices choices) (position+2)
      ⟨s,.host (.draft none),.wasm suspended::.host caller::stack⟩ [.hostExit none]
      ⟨s,.hostReturn none,.wasm suspended::.host caller::stack⟩ := .finish rfl
  have reply : (Spec.HostReply.mk s none).Admissible pending.before pending.results :=
    ⟨by rw [beforeEq];exact Spec.extend_store_refl s (by cases typedStore;assumption),typedStore,by intros values impossible;cases impossible⟩
  have completedStore : (pending.completed ⟨s,none⟩).1.1=s:=Spec.OpenExecution.context_store pending.context _
  have completedCfg : pending.completed ⟨s,none⟩=
      ⟨⟨s,(pending.completed ⟨s,none⟩).1.2⟩,(pending.completed ⟨s,none⟩).2⟩ := by
    generalize eq : pending.completed ⟨s,none⟩=cfg at completedStore ⊢
    rcases cfg with ⟨⟨store,frame⟩,body⟩
    dsimp only at completedStore
    rw [completedStore]
  have resumed : Spec.OpenExecution.ChoiceTransition model (sourceControlChoices choices) (position+3)
      ⟨s,.hostReturn none,.wasm suspended::.host caller::stack⟩ [.completedHost (.call pending.address pending.arguments none)]
      ⟨s,.wasm (pending.completed ⟨s,none⟩).1.2 (pending.completed ⟨s,none⟩).2 (.mk_list []),.host caller::stack⟩ := .resumeWasm reply completedCfg
  obtain ⟨unwindCount,unwind⟩:=pending.trap_unwind_chosen choices.wasm (position+4) s (by cases typedStore;assumption)
  have unwindTrace:=Spec.OpenExecution.ChoiceTrace.wasmCounted model (sourceControlChoices choices) unwind (.mk_list []) (.host caller::stack)
  rw [completedStore] at unwindTrace
  have finishTrace : Spec.OpenExecution.ChoiceTrace model (sourceControlChoices choices) (position+4+unwindCount) 3
      ⟨s,.wasm (pending.context.outerFrame pending.ambient) [.TRAP] (.mk_list []),.host caller::stack⟩
      [.invokeExit .trapped,.hostExit none] ⟨s,.hostReturn none,stack⟩ := by
    exact .next .trap (.next .resumeHost (.next (.finish rfl) (.nil _ _)))
  have rest:=unwindTrace.trans finishTrace
  have body:=Spec.OpenExecution.ChoiceTrace.next enter (.next trapped (.next exited (.next resumed rest)))
  have front:=Spec.OpenExecution.ChoiceTrace.next request (.next accepted normalized)
  rw [Spec.OpenExecution.pending_store,beforeEq] at front
  have whole:=front.trans (by simpa only [position,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using body)
  refine ⟨_,_,whole,?_,?_⟩ <;> simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,true_or,or_true]
end Exec.Theorems.OpenReentrantControl
