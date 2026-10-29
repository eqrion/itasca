import Itasca.Runtime.SourceMachine.Indirect.Definition
import Itasca.Runtime.SourceMachine.Ownership.Bounds
import Itasca.Runtime.SourceMachine.Bound
import Itasca.Runtime.SourceMachine.Core
import Itasca.Runtime.SourceMachine.Float.Descriptor
import Itasca.Runtime.SourceMachine.Stateful.Descriptor
import Itasca.Runtime.SourceMachine.Stateful.OwnershipStore

/-!
Indirect-call ownership and transport through store/code bounds, used by supported and cumulative execution.
-/

/-! ## Ownership -/

section

namespace Itasca.Runtime.SourceMachine.Indirect
open SpecExt Itasca.Runtime.Spec Itasca.Runtime.SourceMachine.Ownership

theorem invoke_owned {bound s f rest next address after}
    (frame : FrameOwned bound f) (frames : ∀item∈rest,FrameOwned bound item)
    (results : ValuesOwned bound s.results)
    (stepped : invoke s f rest address after=.next next) : StateOwned bound next := by
  simp only [invoke] at stepped
  repeat' first | split at stepped | contradiction
  cases stepped
  refine ⟨results,?_⟩
  simp only [List.mem_cons,forall_eq_or_imp]
  refine ⟨⟨values_owned_append.mpr ⟨frame.2.drop _,?_⟩,values_owned_nil _⟩,⟨frame.1,frame.2.take _⟩,frames⟩
  apply default_locals_ownership
  assumption

theorem step_owned {bound s f rest next table type after}
    (frame : FrameOwned bound f) (frames : ∀item∈rest,FrameOwned bound item)
    (results : ValuesOwned bound s.results)
    (stepped : step s f rest table type after=.next next) : StateOwned bound next := by
  unfold step at stepped
  split at stepped
  · cases stepped
  · rename_i front value popped
    split at stepped
    · cases stepped
    · split at stepped
      · cases stepped
      · apply invoke_owned (f:={f with vals:=front}) ⟨frame.1,?_⟩ frames results stepped
        exact (frame.2.pop popped).1
end Itasca.Runtime.SourceMachine.Indirect

end

/-! ## Transport -/

section

namespace Itasca.Runtime.SourceMachine.Indirect
open SpecExt Itasca.Runtime.Spec Itasca.Runtime.SourceMachine.Ownership

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

end Itasca.Runtime.SourceMachine.Indirect

end
