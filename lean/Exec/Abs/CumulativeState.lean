import Exec.Abs.Cumulative
namespace Exec.Abs
def FrameCumulative (f : AFrame) : Prop :=
  Forall CumulativeInstr f.code ∧ Forall (fun label =>
    Forall CumulativeInstr label.cont ∧ Forall CumulativeInstr label.after) f.labels

/-- Defined bodies use the scalar grammar. Host entries are admitted as syntax;
executing them requires separate host laws and yields an explicit host boundary. -/
def CumulativeFunctions (s : store) : Prop :=
  ∀ function ∈ s.FUNCS, match function.CODE with
    | .HOST _ => True
    | .FUNC _ _ body => Forall CumulativeInstr body

structure CumulativeState (s : AState) : Prop where
  active : Forall FrameCumulative s.frames
  functions : CumulativeFunctions s.store

theorem CumulativeFunctions.same {before after : store}
    (same : after.FUNCS = before.FUNCS) (functions : CumulativeFunctions before) : CumulativeFunctions after := by
  simpa only [CumulativeFunctions, same] using functions

theorem CumulativeState.store_same {state : AState} {after : store}
    (same : after.FUNCS = state.store.FUNCS) (covered : CumulativeState state) :
    CumulativeState {state with store := after} := ⟨covered.active, covered.functions.same same⟩

end Exec.Abs
