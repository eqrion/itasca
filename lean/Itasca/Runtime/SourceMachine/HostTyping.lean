import Itasca.Runtime.SourceMachine.CallSafety
import Itasca.Runtime.SourceMachine.FrameTypingExtension
namespace Itasca.Runtime.Abs
open SpecExt Itasca.Runtime.Spec

/-- A host callback suspends a nonempty source stack with its pending result
signature. The store is the pre-call store until the atomic callback completes. -/
structure HostPending (state : AState) (results : List valtype) : Prop where
  store : wf_store state.store
  functions : FunctionsTyped state.store
  ambient : wf_frame state.ambient
  frames : FramesTyped state.store state.frames results
  nonempty : state.frames ≠ []
  values : state.results = []
  heights : Forall FrameHeights state.frames

/-- Store extension transports every suspended frame; typed callback results
resume the active one. New functions obtain their typing from the post-store
invariant instead of assuming the host cannot add functions. -/
theorem HostPending.resume {state : AState} {types : List valtype}
    (pending : HostPending state types) {after : _root_.store}
    (extension : Extend_store state.store after) (functions : FunctionsTyped after)
    {values : List val} (typed : ResultsTyped after types values) :
    ∃ f rest, state.frames = f :: rest ∧
      ATyped ⟨after,state.ambient,{f with vals := f.vals ++ values} :: rest,[]⟩ := by
  cases frames : state.frames with
  | nil => exact False.elim (pending.nonempty frames)
  | cons f rest =>
    have frameTypes := pending.frames.extend extension
    rw [frames] at frameTypes
    cases frameTypes with
    | cons head tail =>
      have resumed := resume_frame_preservation head typed
      refine ⟨f,rest,rfl,(extend_store_wf extension).2,functions,pending.ambient,
        .cons resumed tail,by simp [Forall],by simp,?_⟩
      intro frame member
      rcases List.mem_cons.mp member with rfl | member
      · exact frameTyped_heights resumed
      · exact pending.heights frame (by rw [frames]; simp [member])

/-- Source typing discharges argument extraction and the host's suspended
continuation directly from the abstract call result. -/
theorem host_call_preparation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (index address : Nat)
    (args : List val) (results : List valtype) (resume : AState)
    (typed : ATyped ⟨s,ambient,{f with code := .CALL (.mk_uN index) :: after} :: rest,[]⟩)
    (step : astep ⟨s,ambient,{f with code := .CALL (.mk_uN index) :: after} :: rest,[]⟩ =
      .host address args results resume) :
    HostPending resume results ∧ ∃ identity params,
      HostFunction s address identity params results ∧ ResultsTyped s params args := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    cases hf with
    | mk C bindings localTypes locals values returns hc hw =>
      simp only [List.append_nil] at hc
      obtain ⟨front, ins, outs, hop, hstack, hafter, heights⟩ :=
        codeStack_after_bounds (value_types_concrete f.vals) hc
      cases hop with
      | call _ _ inputs outputs hi ht _ _ =>
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
          refine ⟨⟨typed.store,typed.functions,typed.ambient,.cons hcaller hr,
            by simp,rfl,?_⟩,identity,ins,?_ ,hargs⟩
          · intro frame member
            rcases List.mem_cons.mp member with rfl | member
            · exact hcallerHeights
            · exact typed.heights frame (by simp [member])
          · refine ⟨fn.MODULE,?_⟩
            have record : fn = ⟨⟨.mk_list ins,.mk_list outs⟩,fn.MODULE,.HOST identity⟩ := by
              cases fn with
              | MKfuncinst ft mm cd =>
                simp only [funcinst.TYPE] at htype'
                simp only [funcinst.CODE] at hcode
                subst ft
                subst cd
                rfl
            rw [← record]
            exact hfn
        | FUNC fi fl body =>
          cases defaults : defaultLocals fl <;>
            simp [astep,call,hresolve,hfn,htype',hbound,hheight,hargtypes,hcode,defaults] at step
end Itasca.Runtime.Abs
