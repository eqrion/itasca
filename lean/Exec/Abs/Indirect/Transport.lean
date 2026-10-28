import Exec.Abs.Indirect.Ownership
import Exec.Abs.Bound
import Exec.Abs.Core
import Exec.Abs.Float.Decode
import Exec.Abs.Stateful.Descriptor
import Exec.Abs.Stateful.OwnershipStore
namespace Itasca.Runtime.Abs.Indirect
open SpecExt Itasca.Runtime.Spec Itasca.Runtime.Abs.Ownership

theorem invoke_metadata {s f rest address after next}
    (stepped : invoke s f rest address after=.next next) :
    next.store=s.store ∧ next.ambient=s.ambient := by
  simp only [invoke] at stepped
  repeat' first | split at stepped | contradiction
  cases stepped
  exact ⟨rfl,rfl⟩

theorem step_metadata {s f rest table type after next}
    (stepped : step s f rest table type after=.next next) :
    next.store=s.store ∧ next.ambient=s.ambient := by
  unfold step at stepped
  repeat' first | split at stepped | contradiction
  exact invoke_metadata stepped

theorem invoke_bound {bound : Nat} {s : AState} {f : AFrame} {rest : List AFrame}
    {address : Nat} {after : List instr} {next : AState}
    (bounded : CodeBound bound s) (tail : sizeOf after≤bound)
    (labels : ∀label∈f.labels,sizeOf (label.cont++label.after)≤bound)
    (frames : Forall (FrameCodeBound bound) rest)
    (stepped : invoke s f rest address after=.next next) : CodeBound bound next := by
  cases lookup : s.store.FUNCS[address]? with
  | none => simp [invoke,lookup] at stepped
  | some fn =>
    have function := bounded.functions fn (List.mem_of_getElem? lookup)
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
            refine ⟨bounded.positive,?_,bounded.functions⟩
            intro frame member
            rcases List.mem_cons.mp member with rfl | member
            · exact ⟨function,by simpa [Forall] using bounded.positive⟩
            · rcases List.mem_cons.mp member with rfl | member
              · exact ⟨tail,labels⟩
              · exact frames frame member

theorem step_bound {bound s ambient f rest table type after next}
    (bounded : CodeBound bound ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
    (stepped : step ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ f rest table type after=.next next) : CodeBound bound next := by
  have frame := bounded.frames {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} (List.mem_cons_self ..)
  unfold step at stepped
  repeat' first | split at stepped | contradiction
  apply invoke_bound (f:={f with vals:=_}) bounded ?_ frame.2 ?_ stepped
  · have size := frame.1
    change sizeOf (.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after)≤bound at size
    simp at size
    omega
  · exact fun item member => bounded.frames item (List.mem_cons_of_mem _ member)

theorem step_stateful_owned {bounds s ambient f rest table type after next}
    (owned : StatefulOwned bounds ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
    (stepped : step ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ f rest table type after=.next next) : StatefulOwned bounds next := by
  have frame := owned.values.2 {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} (List.mem_cons_self ..)
  refine ⟨step_owned frame (fun item member => owned.values.2 item (List.mem_cons_of_mem _ member)) owned.values.1 stepped,?_⟩
  rw [(step_metadata stepped).1]
  exact owned.heap

end Itasca.Runtime.Abs.Indirect
