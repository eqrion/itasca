import Itasca.Profile.BodyExecution
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Oversized function bodies reject before initialization or visitor calls. -/
theorem reader_body_too_large {V} (visitor : code.OpVisitor V) (profile : ValidationProfile)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32) (value : V)
    (large : limits.MAX_FUNCTION_BYTES.val < data.length) :
    CodeEntry.runBody visitor profile data env ctx index value =
      .ok (.Err .BodyTooLarge,value) := by
  have guard : Slice.len data > limits.MAX_FUNCTION_BYTES := by simpa using large
  cases profile <;>
    simp only [CodeEntry.runBody,code.validate_body_with,code.validate_multi_value_body_with,
      code.validate_body_with_profile,guard,↓reduceIte]
end Exec.Code
