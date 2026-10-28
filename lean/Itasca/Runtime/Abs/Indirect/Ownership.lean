import Itasca.Runtime.Abs.Indirect.Definition
import Itasca.Runtime.Abs.Ownership.Bounds
namespace Itasca.Runtime.Abs.Indirect
open SpecExt Itasca.Runtime.Spec Itasca.Runtime.Abs.Ownership

theorem invoke_owned {bound s f rest next address after}
    (frame : FrameOwned bound f) (frames : ∀item∈rest,FrameOwned bound item)
    (results : ValuesOwned bound s.results)
    (stepped : invoke s f rest address after=.next next) : StateOwned bound next := by
  simp only [invoke] at stepped
  repeat' first | split at stepped | contradiction
  cases stepped
  refine ⟨results,?_⟩
  simp only [List.mem_cons,forall_eq_or_imp]
  refine ⟨⟨valuesOwned_append.mpr ⟨frame.2.drop _,?_⟩,valuesOwned_nil _⟩,⟨frame.1,frame.2.take _⟩,frames⟩
  apply defaultLocals_ownership
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
end Itasca.Runtime.Abs.Indirect
