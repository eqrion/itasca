import Itasca.MultiValue.Wasm2Sound
import Itasca.MultiValue.ExtendedSound
import Itasca.MultiValue.StepContext

open Aeneas Aeneas.Std

namespace Itasca.MultiValue

/-- Scalar preservation includes the extracted capacity guard. -/
theorem Pending.scalar_step {data env locals index st} (p : Pending data env locals index st)
    (ctx : code.Context) (hlocals : ctx.locals = locals)
    (opcode : U8) (hscalar : opcode.val ∉ controlOpcodes)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode) :
    step st data env ctx index opcode ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  rw [step.scalar_eq st data env ctx index opcode hscalar]
  split
  · simp
  · rename_i hn
    have hsize : st.core.vals.val.length < Usize.max := by scalar_tac
    obtain ⟨⟨r, s, v⟩, hr, hout⟩ := WP.spec_imp_exists
      (p.wasm2_scalar code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor () FullVisitor.empty_total ctx hlocals
        opcode hscalar hsize hbyte)
    rw [WP.spec_equiv_exists]
    exact ⟨(r, {st with core := s}), by simp [hr], hout⟩

end Itasca.MultiValue
