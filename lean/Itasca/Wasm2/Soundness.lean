import Itasca.Wasm2.SoundLoop
import Itasca.Wasm2.Step.NonControlSound
import Itasca.Wasm2.Control.EnterStep
import Itasca.Wasm2.Control.EndStep
import Itasca.Wasm2.Control.BrTableStep
import Itasca.Wasm2.Control.Return

open Aeneas Aeneas.Std

namespace Itasca.MultiValue

/-- Every opcode preserves semantic control and exact byte provenance on
success. Reserved opcodes and malformed immediates need no input premise. -/
theorem steps (data : Slice U8) (env : module.Env) (locals : alloc.vec.Vec types.ValueType)
    (ctx : code.Context) (index : U32) (hlocals : ctx.locals = locals) :
    Steps data env locals ctx index := by
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

end Itasca.MultiValue

namespace Itasca

/-- The actual public multi-value body validator is sound for independent
binary grammar and generated Wasm 2.0 typing, on arbitrary bytes and contexts. -/
theorem code.validate_multi_value_body.wasm_spec (data : Slice U8) (env : module.Env)
    (locals : alloc.vec.Vec types.ValueType) (index : U32) :
    code.validate_multi_value_body data env locals index ⦃ r =>
      r = .Ok () → MultiValue.Validated data env locals index ⦄ :=
  MultiValue.public_spec_of_steps data env locals index
    (MultiValue.steps data env locals ⟨locals, alloc.vec.Vec.new _⟩ index rfl)

theorem code.validate_multi_value_body.wasm_sound (data : Slice U8) (env : module.Env)
    (locals : alloc.vec.Vec types.ValueType) (index : U32)
    (haccepted : code.validate_multi_value_body data env locals index = .ok (.Ok ())) :
    MultiValue.Validated data env locals index := by
  have hs := code.validate_multi_value_body.wasm_spec data env locals index
  simpa [haccepted] using hs

end Itasca
