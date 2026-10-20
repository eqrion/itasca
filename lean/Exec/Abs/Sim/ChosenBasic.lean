import Exec.Abs.Sim.ChosenTyped
import Exec.Abs.Sim.NeutralDecode
namespace Exec.Abs
open SpecExt Exec.Spec

/-- Reuse a concrete one-step source simulation at its fixed-policy boundary. -/
theorem ChosenNextSim.neutral {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat)
    {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame} {next : AState}
    (source : StepH (decode ⟨s,ambient,f::rest,[]⟩) [] (decode next))
    (neutral : neutralActive (f.code.map admininstr_instr)=true) :
    ChosenNextSim choices occurrence ⟨s,ambient,f::rest,[]⟩ next :=
  .single admissible (chosen_neutral_simulation admissible vector occurrence source neutral)
end Exec.Abs
