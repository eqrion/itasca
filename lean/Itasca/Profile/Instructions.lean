import Itasca.Wasm1.ProfileSyntax

/-!
# Profile instruction restrictions

`Profile.Instructions` is the restriction on instruction trees beyond generated declarative typing:
`Wasm1.Instructions` for Wasm 1.0 and no restriction for Wasm 2.0. `Instructions.congr_labels`
shows it depends on the label context only.
-/

open Aeneas Aeneas.Std

namespace Itasca.Profile

/-- The profile's restriction on an instruction tree. Instruction availability comes from the binary
grammar; Wasm 1.0 additionally requires identical `br_table` target signatures. -/
def Instructions (profile : ValidationProfile) (C : context) (ops : List instr) : Prop :=
  match profile with
  | .Wasm1 => Wasm1.Instructions C ops
  | .Wasm2 => True

/-- The profile restrictions depend only on the label signatures of the context. Other context
fields are governed by generated declarative typing. -/
theorem Instructions.congr_labels {profile : ValidationProfile} {C : context} {ops : List instr}
    (h : Instructions profile C ops) (D : context) (he : C.LABELS = D.LABELS) :
    Instructions profile D ops := by
  cases profile with
  | Wasm1 => exact Wasm1.Instructions.congr_labels h D he
  | Wasm2 => trivial

end Itasca.Profile
