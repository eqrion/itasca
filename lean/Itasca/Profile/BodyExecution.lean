import Itasca.Generated.Funs

open Aeneas Aeneas.Std

namespace Itasca.CodeEntry

/-- The body operation selected by the actual entry validator. This adapter
only names the extracted dispatch; its semantic contracts are independent. -/
def runBody {V : Type} (visitor : code.OpVisitor V) (profile : ValidationProfile)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32) (v : V) :
    Result (core.result.Result Unit error.OpError × V) :=
  match profile with
  | .Wasm1 => code.validate_body_with visitor data env ctx v
  | .MultiValue => code.validate_multi_value_body_with visitor data env ctx index v

/-- Framing is common to both branches of the extracted body dispatch. -/
theorem runBody_slice {V : Type} (visitor : code.OpVisitor V) (profile : ValidationProfile)
    (data : Slice U8) (first last : Usize) (env : module.Env) (ctx : code.Context)
    (index : U32) (v : V) :
    (match profile with
    | .Wasm1 => do
        let body ← core.slice.index.SliceIndexRangeUsizeSlice.index ⟨first, last⟩ data
        let (r, v') ← code.validate_body_with visitor body env ctx v
        .ok (v', r)
    | .MultiValue => do
        let body ← core.slice.index.SliceIndexRangeUsizeSlice.index ⟨first, last⟩ data
        let (r, v') ← code.validate_multi_value_body_with visitor body env ctx index v
        .ok (v', r)) = (do
        let body ← core.slice.index.SliceIndexRangeUsizeSlice.index ⟨first, last⟩ data
        let (r, v') ← runBody visitor profile body env ctx index v
        .ok (v', r)) := by
  cases profile <;> rfl

end Itasca.CodeEntry
