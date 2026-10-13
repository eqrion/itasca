import Itasca.Wasm1.Run
import Itasca.Wasm1.ProfileSyntax

open Aeneas Aeneas.Std

namespace Itasca.Wasm1

/-- The intended input proposition for completeness combines exact bytes,
generated declarative typing, and the version-specific semantic restriction.
The size cap, environment signatures, and API result shape are explicit
additional hypotheses of the public completeness theorem. -/
def Body (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) : Prop :=
  ∃ ops, Wasm.BodyEncoding data ops ∧ Wasm.FunctionTyped env ctx bt ops ∧
    Instructions (WasmFrames.enter (EnvTranslation.context env ctx) .body bt) ops

theorem Body.validated {data env ctx bt} (h : Body data env ctx bt) :
    Wasm.Validated data env ctx bt := by
  obtain ⟨ops, hb, ht, _⟩ := h
  exact ⟨ops, hb, ht⟩

end Itasca.Wasm1
