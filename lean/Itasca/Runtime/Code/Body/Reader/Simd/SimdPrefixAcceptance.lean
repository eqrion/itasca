import Itasca.Runtime.Code.Body.Reader.Simd.ReaderSimdPure
import Itasca.Runtime.Code.Body.Reader.Acceptance.ReaderProfileAcceptance
import Itasca.Binary.Wasm1.EncodingUnique

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Independent decoding selects the exact successful source subopcode run. -/
theorem simd_sub_success_of_decoded {V : Type} (source : code.OpVisitor V)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (before after : V) (sub : U32) (next : Usize)
    (decoded : Leb128.Decoded data st.core.pos sub next)
    (reference : code.step_profile source st data env ctx index .Wasm2 253#u8 before = .ok (.Ok (),out,after)) :
    st.core.vals.val.length < Usize.max ∧
      Wasm2.Simd.subStep source {st.core with pos := next} data env sub before = .ok (.Ok (),out.core,after) := by
  obtain ⟨capacity,actual,position,bytes,called⟩ := simd_prefix_success source st out data env ctx index before after reference
  obtain ⟨rfl,rfl⟩ := bytes.unique decoded
  exact ⟨capacity,called⟩

/-- Replay the actual profile guard and unsigned-LEB prefix with an available
subopcode implementation. The target uses exactly the source-decoded cursor. -/
theorem simd_prefix_available {W : Type} (target : code.OpVisitor W)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (compiler : W) (sub : U32) (next : Usize) (post : W → Prop)
    (decoded : Leb128.Decoded data st.core.pos sub next)
    (capacity : st.core.vals.val.length < Usize.max)
    (acceptance : Wasm2.Simd.subStep target {st.core with pos := next} data env sub compiler
      ⦃ result => result.1 = .Ok () ∧ result.2.1 = out.core ∧ post result.2.2 ⦄) :
    code.step_profile target st data env ctx index .Wasm2 253#u8 compiler
      ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧ post result.2.2 ⦄ := by
  apply profile_scalar_available_wasm2 target st out.core data env ctx index 253#u8 compiler post capacity (by decide)
  rw [code.step_wasm2.simd,code.step_simd.eq_runs]
  have read := reader.read_u32_leb.complete data st.core.pos sub next decoded
  simpa only [Wasm2.Simd.prefixStep,read,bind_ok] using acceptance

end Itasca.Runtime.Code
