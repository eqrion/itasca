import Itasca.Body.Wasm1ProfileTransport

open Aeneas Aeneas.Std

namespace Itasca.Profile

/-- Instruction availability is determined by the independent binary grammar.
The Wasm 1.0 case also retains its stricter branch-table typing rule. -/
def Instructions (profile : ValidationProfile) (C : context) (ops : List instr) : Prop :=
  match profile with
  | .Wasm1 => Wasm1.Instructions C ops
  | .Wasm2 => True

/-- Current version-specific instruction restrictions observe label signatures.
Other context fields remain governed by generated declarative typing. -/
theorem Instructions.congr_labels {profile : ValidationProfile} {C : context} {ops : List instr}
    (h : Instructions profile C ops) (D : context) (he : C.LABELS = D.LABELS) :
    Instructions profile D ops := by
  cases profile with
  | Wasm1 => exact Wasm1.Instructions.congr_labels h D he
  | Wasm2 => trivial

end Itasca.Profile
