import Itasca.Wasm2.EmptyVisitorLoop
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Oversized function bodies reject before initialization or visitor calls. -/
theorem reader_body_too_large {V} (visitor : code.OpVisitor V) (profile : ValidationProfile)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32) (value : V)
    (large : limits.MAX_FUNCTION_BYTES.val < data.length) :
    code.validate_body_with visitor data env ctx index profile value =
      .ok (.Err .BodyTooLarge,value) := by
  have guard : Slice.len data > limits.MAX_FUNCTION_BYTES := by simpa using large
  simp only [code.validate_body_with,guard,↓reduceIte]
end Itasca.Runtime.Code
