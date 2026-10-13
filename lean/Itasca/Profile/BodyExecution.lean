import Itasca.Generated.Funs

/-!
# Profile body dispatch

`CodeEntry.runBody` names the extracted body validator that the code-entry pipeline selects for a
profile, and `runBody_slice` frames it inside a slice-indexing step.
-/

open Aeneas Aeneas.Std

namespace Itasca.CodeEntry

/-- The extracted body validator selected by profile: `code.validate_body_with` for Wasm 1.0 and
`code.validate_multi_value_body_with` for Wasm 2.0. -/
def runBody {V : Type} (visitor : code.OpVisitor V) (profile : ValidationProfile)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32) (v : V) :
    Result (core.result.Result Unit error.OpError × V) :=
  match profile with
  | .Wasm1 => code.validate_body_with visitor data env ctx v
  | .Wasm2 => code.validate_multi_value_body_with visitor data env ctx index v

/-- Indexing the data slice before the dispatch commutes with `runBody` for both profiles. -/
theorem runBody_slice {V : Type} (visitor : code.OpVisitor V) (profile : ValidationProfile)
    (data : Slice U8) (first last : Usize) (env : module.Env) (ctx : code.Context)
    (index : U32) (v : V) :
    (match profile with
    | .Wasm1 => do
        let body ← core.slice.index.SliceIndexRangeUsizeSlice.index ⟨first, last⟩ data
        let (r, v') ← code.validate_body_with visitor body env ctx v
        .ok (v', r)
    | .Wasm2 => do
        let body ← core.slice.index.SliceIndexRangeUsizeSlice.index ⟨first, last⟩ data
        let (r, v') ← code.validate_multi_value_body_with visitor body env ctx index v
        .ok (v', r)) = (do
        let body ← core.slice.index.SliceIndexRangeUsizeSlice.index ⟨first, last⟩ data
        let (r, v') ← runBody visitor profile body env ctx index v
        .ok (v', r)) := by
  cases profile <;> rfl

end Itasca.CodeEntry
