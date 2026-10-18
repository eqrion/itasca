import Exec.Abs.HostCallSite
import Exec.Abs.Indirect.HostTyping
import Exec.Abs.Indirect.HostSimulation
namespace Exec.Abs.Indirect
open SpecExt Exec.Spec

/-- The actual abstract indirect-host outcome resumes its typed saved stack
and matches the atomic source host event after checked table resolution. -/
theorem host_return_correct (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (table type : Nat) (after : List instr) (address : Nat)
    (args : List val) (results : List valtype) (resume : AState)
    (typed : ATyped ⟨s,ambient,{f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
    (stepped : step ⟨s,ambient,{f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩
      f rest table type after = .host address args results resume)
    (fresh : store) (extension : Extend_store s fresh) (functions : FunctionsTyped fresh)
    (returned : List val) (checked : ResultsTyped fresh results returned) :
    ATyped (finishHost resume fresh returned) ∧
      StepsHN 2 (decode ⟨s,ambient,{f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
        [.call address args (some returned)] (decode (finishHost resume fresh returned)) := by
  obtain ⟨pending,identity,params,front,position,host,arguments,split,resumeEq,target,tableBound,typeBound,
      positionBound,frameWf,labels,frontWf,tail,callers,heights⟩ :=
    host_preparation s ambient f rest table type after address args results resume typed stepped
  refine ⟨pending.finish_typed (by simpa only [resumeEq] using extension) functions checked,?_⟩
  have atomic := host_return_step host arguments extension checked frameWf
  have source := host_return_simulation s fresh ambient f rest after table type position address front args returned
    _ typed.store typed.ambient frameWf labels frontWf tail callers heights target tableBound typeBound positionBound
    (resultsTyped_wf arguments) atomic
  simpa only [finishHost,resumeEq,←split] using source

/-- An indirect host trap retains its post-callback store and emits exactly
one host event while the source semantics unwinds every caller. -/
theorem host_trap_correct (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (table type : Nat) (after : List instr) (address : Nat)
    (args : List val) (results : List valtype) (resume : AState)
    (typed : ATyped ⟨s,ambient,{f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
    (stepped : step ⟨s,ambient,{f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩
      f rest table type after = .host address args results resume)
    (fresh : store) (extension : Extend_store s fresh) :
    ∃ n, 2 ≤ n ∧ StepsHN n
      (decode ⟨s,ambient,{f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
      [.call address args none] ⟨⟨fresh,ambient⟩,[.TRAP]⟩ := by
  obtain ⟨pending,identity,params,front,position,host,arguments,split,resumeEq,target,tableBound,typeBound,
      positionBound,frameWf,labels,frontWf,tail,callers,heights⟩ :=
    host_preparation s ambient f rest table type after address args results resume typed stepped
  have atomic := host_trap_step host arguments extension frameWf
  have source := host_trap_simulation s fresh ambient f rest after table type position address front args _
    typed.store (extend_store_wf extension).2 typed.ambient frameWf labels frontWf tail callers heights
    target tableBound typeBound positionBound (resultsTyped_wf arguments) atomic
  simpa only [←split] using source
end Exec.Abs.Indirect
