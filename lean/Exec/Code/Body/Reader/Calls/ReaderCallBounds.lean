import Exec.Code.Body.Reader.Common.ReaderSafety
import Exec.Code.Body.Reader.Calls.ReaderWasm2Call
import Itasca.Wasm2.Control.Total
import Itasca.Wasm2.Scalar.ReadersTotal
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxHeartbeats 2000000
attribute [local step] code.pop_with_type.total code.pop_types.total code.require_single_result.spec
  Wasm2.ScalarReaders.reserved_zero

theorem reader_call_info_bound (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (shape : Control.Shape st.core) :
    code.call_info st data env ⦃ out => ∀ index, out.1 = .Ok index →
      index.val < env.func_types.val.length ⦄ := by
  unfold code.call_info
  step*

theorem reader_call_indirect_info_bound (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (shape : Control.Shape st.core) :
    code.call_indirect_info st data env ⦃ out => ∀ index table, out.1 = .Ok (index,table) →
      index.val < env.types.val.length ⦄ := by
  unfold code.call_indirect_info
  step*

theorem reader_call_bound (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.read_call st data env ⦃ out => ∀ index, out.1 = .Ok index →
      index.val < env.func_types.val.length ⦄ := by
  unfold code.read_call
  step* <;> simp_all [alloc.vec.Vec.deref,Slice.length,Slice.from_val]
  cases r1 <;> simp_all <;> omega

theorem reader_call_indirect_bound (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.read_call_indirect st data env ⦃ out => ∀ index, out.1 = .Ok index →
      index.val < env.types.val.length ⦄ := by
  unfold code.read_call_indirect
  simp only [alloc.vec.Vec.is_empty]
  step* <;> simp_all [alloc.vec.Vec.deref,Slice.length,Slice.from_val] <;> try omega
  all_goals try (cases r2 <;> simp_all <;> omega)
  all_goals simpa only [List.length_pos_iff] using (by assumption : env.table_types.val ≠ [])
end Exec.Code
