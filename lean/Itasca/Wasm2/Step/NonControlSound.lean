import Itasca.Wasm2.Step.Sound
import Itasca.Wasm2.NumericExt.Sound
import Itasca.Wasm2.Step.Context

/-!
# Soundness of the non-control opcodes

`Pending.scalar_step` shows that every non-control opcode, including the capacity guard in front
of `code.step_wasm2`, preserves `Pending` on success.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- Every non-control opcode preserves `Pending` on success. The extracted capacity guard is
included. -/
theorem Pending.scalar_step {data env profile locals index st} (p : Pending data env profile locals index st)
    (ctx : code.Context) (hlocals : ctx.locals = locals)
    (opcode : U8) (hscalar : opcode.val ∉ controlOpcodes)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode) :
    step st data env profile ctx index opcode ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  rw [step.scalar_eq st data env profile ctx index opcode hscalar]
  split
  · simp
  · rename_i hn
    have hsize : st.core.vals.val.length < Usize.max := by scalar_tac
    obtain ⟨⟨r, s, v⟩, hr, hout⟩ := WP.spec_imp_exists
      (p.wasm2_scalar code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor () FullVisitor.empty_total ctx hlocals
        opcode hscalar hsize hbyte)
    rw [WP.spec_equiv_exists]
    exact ⟨(r, {st with core := s}), by simp [hr], hout⟩

end Itasca.Wasm2
