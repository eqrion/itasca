import Itasca.Generated.Funs

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- Opcodes whose control effects are handled by the multi-value dispatcher. -/
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
