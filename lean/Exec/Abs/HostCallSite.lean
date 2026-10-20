import Exec.Abs.HostTyping
import Exec.Abs.Sim.Call
import Exec.Abs.Sim.Host
import Exec.Spec.HostCall
namespace Exec.Abs
open SpecExt Exec.Spec

/-- The source context around an abstract host boundary is recovered from
instruction typing and actual address/argument extraction. -/
theorem host_call_site (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (index address : Nat)
    (args : List val) (results : List valtype) (resume : AState)
    (typed : ATyped ⟨s,ambient,{f with code := .CALL (.mk_uN index) :: after} :: rest,[]⟩)
    (step : astep ⟨s,ambient,{f with code := .CALL (.mk_uN index) :: after} :: rest,[]⟩ =
      .host address args results resume) :
    ∃ front, f.vals = front ++ args ∧
      resume = ⟨s,ambient,{f with vals := front,code := after} :: rest,[]⟩ ∧
      f.module.FUNCS[index]? = some address ∧ index < 2^32 ∧
      wf_frame f.toFrame ∧ LabelsWf f.labels ∧ Forall wf_val front ∧
      Forall wf_instr after ∧ Forall FrameWf rest ∧
      (∀ label ∈ f.labels, label.height ≤ front.length) := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    cases hf with
    | mk C bindings localTypes locals values returns hc hw =>
      simp only [List.append_nil] at hc
      obtain ⟨front, ins, outs, hop, hstack, hafter, heights⟩ :=
        codeStack_after_bounds (value_types_concrete f.vals) hc
      cases hop with
      | call _ _ inputs outputs hi ht _ wfInstruction =>
        simp only [labelContext, proj_uN_0] at hi ht
        have hi' : index < f.module.FUNCS.length := by
          rw [bindings.funcs.length_eq]
          exact hi
        obtain ⟨fn, hfn, htype⟩ := bindings.funcs.get hi' hi
        simp only [List.get_eq_getElem] at hfn htype
        have htype' : fn.TYPE = ⟨.mk_list ins, .mk_list outs⟩ := by
          rw [htype]
          simpa only [getElem!_pos C.FUNCS index hi] using ht
        have hresolve := List.getElem?_eq_getElem hi'
        have hlen := congrArg List.length hstack
        simp only [List.length_map, List.length_append] at hlen
        have hheight : f.vals.length - ins.length = front.length := by omega
        have hbound : ins.length ≤ f.vals.length := by omega
        have hargs : ResultsTyped s ins (f.vals.drop front.length) := by
          apply resultsTyped_drop (before := front)
          simpa only [hstack] using values
        have hargtypes := results_type_of_typed hargs
        have hfront : (f.vals.take front.length).map valueType = front := by
          rw [List.map_take, hstack, List.take_left]
        have hcaller : FrameTyped s { f with vals := f.vals.take front.length, code := after } outs := by
          apply FrameTyped.mk (f := { f with vals := f.vals.take front.length, code := after }) C
            bindings localTypes locals (resultsTyped_take front.length values) returns ?_ hw
          simpa only [hfront] using hafter
        have hcallerHeights : FrameHeights { f with vals := f.vals.take front.length, code := after } := by
          intro label hm
          have hh := heights label hm
          simp only [List.length_take]
          omega
        cases hcode : fn.CODE with
        | HOST identity =>
          have observed := step
          simp [astep,call,hresolve,hfn,htype',hbound,hheight,hargtypes,hcode] at observed
          obtain ⟨rfl,rfl,rfl,rfl⟩ := observed
          refine ⟨f.vals.take front.length,(List.take_append_drop _ _).symm,rfl,hresolve,?_,hw,
            codeStack_labels_wf hc,?_,?_,framesTyped_wf hr,hcallerHeights⟩
          · cases wfInstruction with
            | instr_case_10 _ bounded => cases bounded with
              | uN_case_0 _ bounds => norm_num at bounds ⊢; omega
          · exact fun value member => resultsTyped_wf values value (List.mem_of_mem_take member)
          · exact fun instruction member => codeStack_wf hc instruction (by simp [member])
        | FUNC fi fl body =>
          cases defaults : defaultLocals fl <;>
            simp [astep,call,hresolve,hfn,htype',hbound,hheight,hargtypes,hcode,defaults] at step
/-- Resume the exact source continuation stored by the host boundary. -/
def finishHost (pending : AState) (after : store) (values : List val) : AState :=
  {pending with store := after, frames := match pending.frames with
    | [] => []
    | f :: rest => {f with vals := f.vals ++ values} :: rest}

theorem HostPending.finish_typed {state : AState} {types : List valtype}
    (pending : HostPending state types) {after : _root_.store}
    (extension : Extend_store state.store after) (functions : FunctionsTyped after)
    {values : List val} (typed : ResultsTyped after types values) :
    ATyped (finishHost state after values) := by
  obtain ⟨f,rest,frames,valid⟩ := pending.resume extension functions typed
  simpa only [finishHost,frames,pending.values] using valid

/-- A typed abstract host result resumes its exact saved continuation and
performs two labeled source steps, without assumptions about host result types
before the runtime check or restrictions on newly added functions. -/
theorem host_call_return_correct (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (index address : Nat)
    (args : List val) (results : List valtype) (resume : AState)
    (typed : ATyped ⟨s,ambient,{f with code := .CALL (.mk_uN index) :: after} :: rest,[]⟩)
    (step : astep ⟨s,ambient,{f with code := .CALL (.mk_uN index) :: after} :: rest,[]⟩ =
      .host address args results resume)
    (fresh : store) (extension : Extend_store s fresh) (sourceTyped : Store_ok fresh) (functions : FunctionsTyped fresh)
    (returned : List val) (checked : ResultsTyped fresh results returned) :
    ATyped (finishHost resume fresh returned) ∧
      StepsHN 2 (decode ⟨s,ambient,{f with code := .CALL (.mk_uN index) :: after} :: rest,[]⟩)
        [.call address args (some returned)] (decode (finishHost resume fresh returned)) := by
  obtain ⟨pending,identity,params,host,arguments⟩ :=
    host_call_preparation s ambient f rest after index address args results resume typed step
  obtain ⟨front,split,resumeEq,resolve,bound,frameWf,labels,frontWf,tail,callers,heights⟩ :=
    host_call_site s ambient f rest after index address args results resume typed step
  refine ⟨pending.finish_typed (by simpa only [resumeEq] using extension) functions checked,?_⟩
  have atomic := host_return_step host arguments extension sourceTyped checked frameWf
  have source := host_return_simulation s fresh ambient f rest after index address front args returned
    _ typed.store typed.ambient frameWf labels frontWf tail callers heights resolve bound
    (resultsTyped_wf arguments) atomic
  simpa only [finishHost,resumeEq,← split] using source

/-- A host rejection traps after its completed store effects, then unwinds
all source frames without adding events. -/
theorem host_call_trap_correct (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (index address : Nat)
    (args : List val) (results : List valtype) (resume : AState)
    (typed : ATyped ⟨s,ambient,{f with code := .CALL (.mk_uN index) :: after} :: rest,[]⟩)
    (step : astep ⟨s,ambient,{f with code := .CALL (.mk_uN index) :: after} :: rest,[]⟩ =
      .host address args results resume)
    (fresh : store) (extension : Extend_store s fresh) (sourceTyped : Store_ok fresh) :
    ∃ n, 2 ≤ n ∧ StepsHN n
      (decode ⟨s,ambient,{f with code := .CALL (.mk_uN index) :: after} :: rest,[]⟩)
      [.call address args none] ⟨⟨fresh,ambient⟩,[.TRAP]⟩ := by
  obtain ⟨pending,identity,params,host,arguments⟩ :=
    host_call_preparation s ambient f rest after index address args results resume typed step
  obtain ⟨front,split,resumeEq,resolve,bound,frameWf,labels,frontWf,tail,callers,heights⟩ :=
    host_call_site s ambient f rest after index address args results resume typed step
  have atomic := host_trap_step host arguments extension sourceTyped frameWf
  have source := host_trap_simulation s fresh ambient f rest after index address front args _
    typed.store (extend_store_wf extension).2 typed.ambient frameWf labels frontWf tail callers heights
    resolve bound (resultsTyped_wf arguments) atomic
  simpa only [← split] using source
end Exec.Abs

