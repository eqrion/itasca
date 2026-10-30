import Itasca.Wasm2.SoundLoop
import Itasca.Wasm2.Step.NonControlSound
import Itasca.Wasm2.Control.EnterStep
import Itasca.Wasm2.Control.EndStep
import Itasca.Wasm2.Control.BranchStep
import Itasca.Wasm2.Control.Return

/-!
# Wasm 2.0 body soundness

Discharges `Steps` for every opcode by dispatching to the non-control, block entry, `end`,
branch and `return` families, and concludes `code.bodyCore.sound`: a body accepted under a profile
is `Wasm2.Validated` for that profile, that is, has a binary-grammar encoding typed by the
generated Wasm 2.0 rules, and for Wasm 1.0 also the Wasm 1.0 grammar and restrictions.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- Every opcode preserves semantic control and exact byte provenance on
success. Reserved opcodes and malformed immediates need no input premise. -/
theorem steps (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (locals : alloc.vec.Vec wasm_types.ValueType) (ctx : code.Context) (index : U32)
    (hlocals : ctx.locals = locals) : Steps data env profile locals ctx index := by
  intro st p
  generalize hbyte : data.val[p.start.val]'p.inbounds = opcode
  by_cases hs : opcode.val ∉ controlOpcodes
  · exact p.scalar_step ctx hlocals opcode hs hbyte
  · have hm := Classical.not_not.mp hs
    obtain ⟨⟨n, hn⟩⟩ := opcode
    change n ∈ controlOpcodes at hm
    simp only [controlOpcodes, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h | h <;> subst n
    · simpa [step, Frames.Form.kind] using p.enter_after .block (Or.inl rfl) hbyte
    · simpa [step, Frames.Form.kind] using p.enter_after .loop (Or.inr (Or.inl rfl)) hbyte
    · simpa [step, Frames.Form.kind] using p.enter_after .then_ (Or.inr (Or.inr rfl)) hbyte
    · simpa [step] using p.end_after true 0x05#u8 rfl hbyte
    · simpa [step] using p.end_after false 0x0B#u8 rfl hbyte
    · simpa [step] using p.branch hbyte
    · simpa [step] using p.branch_if hbyte
    · simpa [step] using p.branch_table hbyte
    · simpa [step] using p.return_ hbyte
    · simpa [step] using p.call hbyte
    · simpa [step] using p.call_indirect hbyte

end Itasca.Wasm2

namespace Itasca

/-- `code.bodyCore` is sound for either profile, on arbitrary bytes and contexts. -/
theorem code.bodyCore.spec (data : Slice U8) (env : metadata.Env)
    (locals results : alloc.vec.Vec wasm_types.ValueType) (index : U32) (profile : ValidationProfile) :
    code.bodyCore data env locals results index profile ⦃ r =>
      r = .Ok () → Wasm2.Validated profile data env locals index ⦄ :=
  Wasm2.public_spec_of_steps data env profile locals results index
    (Wasm2.steps data env profile locals ⟨locals, results⟩ index rfl)

theorem code.bodyCore.sound (data : Slice U8) (env : metadata.Env)
    (locals results : alloc.vec.Vec wasm_types.ValueType) (index : U32) (profile : ValidationProfile)
    (haccepted : code.bodyCore data env locals results index profile = .ok (.Ok ())) :
    Wasm2.Validated profile data env locals index := by
  have hs := code.bodyCore.spec data env locals results index profile
  simpa [haccepted] using hs

end Itasca
