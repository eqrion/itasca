import Itasca.Runtime.Abs.HostTyping
import Itasca.Runtime.Abs.Sim.Call
import Itasca.Runtime.Abs.Sim.Host
import Itasca.Runtime.Spec.HostCall
namespace Itasca.Runtime.Abs
open SpecExt Itasca.Runtime.Spec

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

end Itasca.Runtime.Abs

