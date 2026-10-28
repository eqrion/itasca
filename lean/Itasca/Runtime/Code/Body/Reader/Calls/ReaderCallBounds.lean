import Itasca.Runtime.Code.Body.Reader.Common.ReaderSafety
import Itasca.Runtime.Code.Body.Reader.Calls.ReaderWasm2Call
import Itasca.Wasm2.Control.Total
import Itasca.Wasm2.Scalar.ReadersTotal
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
set_option maxHeartbeats 2000000
attribute [local step] code.pop_with_type.total code.pop_types.total
  Wasm2.ScalarReaders.reserved_zero

theorem reader_call_info_bound (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (shape : Control.Shape st.core) :
    code.call_info st data env ⦃ out => ∀ index, out.1 = .Ok index →
      index.val < env.func_types.val.length ⦄ := by
  unfold code.call_info
  step*

theorem reader_call_indirect_info_bound (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (shape : Control.Shape st.core) :
    code.call_indirect_info st data env .Wasm2 ⦃ out => ∀ index table, out.1 = .Ok (index,table) →
      index.val < env.types.val.length ⦄ := by
  unfold code.call_indirect_info
  step*

end Itasca.Runtime.Code
