import Exec.Abs.Indirect.Transport
import Exec.Abs.SupportedState

namespace Exec.Abs.Indirect

theorem invoke_supported {s : AState} {f : AFrame} {rest : List AFrame} {address after next}
    (functions : FunctionsSupported allowed s.store) (tail : Forall allowed after)
    (labels : Forall (fun label => Forall allowed label.cont ∧ Forall allowed label.after) f.labels)
    (frames : Forall (FrameSupported allowed) rest)
    (stepped : invoke s f rest address after=.next next) : SupportedState allowed next := by
  cases lookup : s.store.FUNCS[address]? with
  | none => simp [invoke,lookup] at stepped
  | some fn =>
    have function := functions fn (List.mem_of_getElem? lookup)
    cases signature : fn.TYPE with
    | mk_functype params results =>
      cases params with
      | mk_list params =>
        cases results with
        | mk_list results =>
          cases body : fn.CODE with
          | HOST host =>
            simp only [invoke,lookup,signature,body] at stepped
            repeat' first | split at stepped | contradiction
          | FUNC index locals source =>
            simp only [body] at function
            simp only [invoke,lookup,signature,body] at stepped
            repeat' first | split at stepped | contradiction
            cases stepped
            refine ⟨?_,functions⟩
            intro frame member
            rcases List.mem_cons.mp member with rfl | member
            · exact ⟨function,by simp [Forall]⟩
            · rcases List.mem_cons.mp member with rfl | member
              · exact ⟨tail,labels⟩
              · exact frames frame member

theorem step_supported {s ambient f rest table type after next}
    (covered : SupportedState allowed ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
    (stepped : step ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ f rest table type after=.next next) : SupportedState allowed next := by
  have frame := covered.active {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} (List.mem_cons_self ..)
  unfold step at stepped
  repeat' first | split at stepped | contradiction
  exact invoke_supported (f:={f with vals:=_}) covered.functions (fun item member => frame.1 item (List.mem_cons_of_mem _ member)) frame.2
    (fun item member => covered.active item (List.mem_cons_of_mem _ member)) stepped


end Exec.Abs.Indirect
