import Itasca.Generated.Funs

/-!
# Scalar context independence

`Wasm2.controlOpcodes` lists the opcodes that the body loop dispatches itself, and
`scalar_context` shows that the shared `code.step` arms for all other opcodes use only the locals
of the context.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- Opcodes whose control effects are handled by the body loop rather than `code.step`:
`block`, `loop`, `if`, `else`, `end`, `br`, `br_if`, `br_table`, `return`, `call` and
`call_indirect`. -/
def controlOpcodes : List Nat := [2, 3, 4, 5, 11, 12, 13, 14, 15, 16, 17]

/-- Shared scalar dispatch observes local types but never function results. -/
theorem scalar_context {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (ctx ctx' : code.Context) (opcode : U8) (v : V)
    (hscalar : opcode.val ∉ controlOpcodes) (hlocals : ctx.locals = ctx'.locals) :
    code.step visitor st data env ctx opcode v =
      code.step visitor st data env ctx' opcode v := by
  unfold code.step
  split <;> first
    | rfl
    | exact False.elim (hscalar (by decide))
    | simp only [code.read_local_get, code.read_local_set, code.read_local_tee,
        code.take_local, code.local_type, hlocals]

end Itasca.Wasm2
