import Itasca.Profile.Types
import Itasca.Wasm2.BodySpec

/-!
# Function-body grammar

`BodyEncoding` describes exact Wasm 2.0 body bytes. The shared semantic
certificate is `Wasm2.Validated`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Profile

/-- The grammar relates the exact body bytes, including the final `end`, to the
instruction tree `ops`. It does not execute the validator or impose implementation limits. -/
def BodyEncoding (data : Slice U8) (ops : List instr) : Prop :=
  Wasm2.BodyEncoding data ops

end Itasca.Profile
