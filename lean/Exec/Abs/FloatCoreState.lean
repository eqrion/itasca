import Exec.Abs.FloatCore
namespace Exec.Abs
def FrameFloatCore (f : AFrame) : Prop :=
  Forall FloatCoreInstr f.code ∧ Forall (fun label =>
    Forall FloatCoreInstr label.cont ∧ Forall FloatCoreInstr label.after) f.labels

/-- Defined bodies use the scalar grammar. Host entries are admitted as syntax;
executing them requires separate host laws and yields an explicit host boundary. -/
def FloatCoreFunctions (s : store) : Prop :=
  ∀ function ∈ s.FUNCS, match function.CODE with
    | .HOST _ => True
    | .FUNC _ _ body => Forall FloatCoreInstr body

structure FloatCoreState (s : AState) : Prop where
  active : Forall FrameFloatCore s.frames
  functions : FloatCoreFunctions s.store

theorem FloatCoreFunctions.same {before after : store}
    (same : after.FUNCS = before.FUNCS) (functions : FloatCoreFunctions before) : FloatCoreFunctions after := by
  simpa only [FloatCoreFunctions, same] using functions

theorem FloatCoreState.store_same {state : AState} {after : store}
    (same : after.FUNCS = state.store.FUNCS) (covered : FloatCoreState state) :
    FloatCoreState {state with store := after} := ⟨covered.active, covered.functions.same same⟩

end Exec.Abs
